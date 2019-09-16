open Util

module Ty : sig
  type t
  type view = Bool | Rat | Unin of ID.t | Arrow of t * t
  val view : t -> view
  val equal : t -> t -> bool
  val hash : t -> int
  val bool : t
  val rat : t
  val unin : ID.t -> t
  val arrow : t -> t -> t
  val arrow_l : t list -> t -> t
  val open_ : t -> t list * t
  val pp : t Fmt.printer
  type env = t Str_map.t
  val parse : env -> t P.t
end = struct
  type t = {
    mutable id: int;
    view: view;
  }
  and view = Bool | Rat | Unin of ID.t | Arrow of t * t

  let view t = t.view
  let equal a b = a.id = b.id
  let hash a = CCInt.hash a.id

  module H = Hashcons.Make(struct
      type nonrec t = t
      let equal a b = match view a, view b with
        | Bool, Bool
        | Rat, Rat -> true
        | Unin a, Unin b -> ID.equal a b
        | Arrow (a1,a2), Arrow (b1,b2) -> equal a1 b1 && equal a2 b2
        | (Bool | Rat | Unin _ | Arrow _), _ -> false
      let hash t = match view t with
        | Bool -> 1
        | Rat -> 2
        | Unin id -> CCHash.combine2 10 (ID.hash id)
        | Arrow (a, b) -> CCHash.combine3 20 (hash a) (hash b)

      let set_id t id = assert (t.id < 0); t.id <- id
      end)

  let mk_ = 
    let h = H.create ~size:32 () in
    fun view -> H.hashcons h {view; id= -1}
  let bool : t = mk_ Bool
  let rat : t = mk_ Rat
  let unin id : t = mk_ @@ Unin id
  let arrow a b = mk_ @@ Arrow (a,b)
  let arrow_l a b = List.fold_right arrow a b
  let rec open_ ty = match view ty with
    | Arrow (a,b) ->
      let args, ret = open_ b in
      a :: args, ret
    | _ -> [], ty
  let rec pp out t = match view t with
    | Bool -> Fmt.string out "bool"
    | Rat -> Fmt.string out "rat"
    | Unin id -> ID.pp_name out id
    | Arrow (a,b) -> Fmt.fprintf out "(@[->@ %a@ %a@])" pp a pp b

  type env = t Str_map.t
  let parse env =
    let open P in
    fix (fun self ->
      (try_ (skip_white *> string "bool") *> return bool) <|>
      (try_ (skip_white *> string "rat") *> return rat) <|>
      (try_ (skip_white *> U.word) >>= fun s ->
       (match Str_map.get s env with
        | Some ty -> return ty
        | None -> failf "not in scope: type %S" s)) <|>
      (try_ (skip_white *> char '(') *> skip_white *>
       string "->" *> skip_white *>
       (parsing "arrow argument" self <* skip_white
        >>= fun a -> many (self <* skip_white) >|= fun rest ->
        match List.rev (a::rest) with
        | [] -> assert false
        | [ret] -> ret
        | ret :: args -> arrow_l (List.rev args) ret)
       <* skip_white <* char ')')
      )
end

module Var : sig
  type t = {id: ID.t; ty: Ty.t}
  val make : ID.t -> Ty.t -> t
  val id : t -> ID.t
  val name : t -> string
  val ty : t -> Ty.t
  val equal : t -> t -> bool
  val hash : t -> int
  val pp : t Fmt.printer

  type env = t Str_map.t
  val parse : env -> t P.t
  val parse_string : env -> string -> t P.t
end = struct
  type t = {id: ID.t; ty: Ty.t}
  let id v = v.id
  let ty v = v.ty
  let name v = ID.name @@ id v
  let make id ty : t = {id; ty}
  let equal a b = ID.equal a.id b.id
  let hash a = ID.hash a.id
  let pp out a = ID.pp_name out a.id

  type env = t Str_map.t
  let parse_string env s =
    try P.return (Str_map.find s env)
    with Not_found -> P.failf "not in scope: variable %S" s
  let parse env : t P.t =
    let open P.Infix in
    P.try_ P.U.word >>= parse_string env
end

module Env = struct
  type t = {
    ty: Ty.env;
    vars: Var.env;
  }

  let empty : t = {ty=Str_map.empty; vars=Str_map.empty; }

  let add_ty (id:ID.t) (env:t) : t =
    if Str_map.mem (ID.name id) env.ty then (
      Util.errorf "cannot shadow type %a" ID.pp_name id;
    );
    {env with ty=Str_map.add (ID.name id) (Ty.unin id) env.ty}

  let add_var (v:Var.t) (env:t) : t =
    if Str_map.mem (Var.name v) env.vars then (
      Util.errorf "cannot shadow fun %a" ID.pp_name (Var.id v);
    );
    {env with vars=Str_map.add (Var.name v) v env.vars}

  type item = Ty of Ty.t | Fun of Var.t

  let to_iter (self:t) : item Iter.t =
    Iter.append
      (Str_map.values self.ty |> Iter.map (fun ty -> Ty ty))
      (Str_map.values self.vars |> Iter.map (fun f -> Fun f))

  let pp out (self:t) =
    let pp_item out = function
      | Ty id -> Fmt.fprintf out "(@[<2>ty@ %a@])" Ty.pp id
      | Fun v -> Fmt.fprintf out "(@[<2>fun@ %a@ %a@])" Var.pp v Ty.pp (Var.ty v)
    in
    Fmt.fprintf out "(@[%a@])" (Util.pp_iter pp_item) (to_iter self)
end

module Term : sig
  type t
  type view =
    | Bool of bool
    | Not of t
    | Eq of t * t
    | App of Var.t * t list

  val view : t -> view
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
  val ty : t -> Ty.t

  val bool : bool -> t
  val true_ : t
  val false_ : t
  val const : Var.t -> t
  val app : Var.t -> t list -> t
  val eq : t -> t -> t
  val neq : t -> t -> t
  val not_ : t -> t
  val abs : t -> t

  val pp : t Fmt.printer

  val parse : Env.t -> t P.t

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t
end = struct
  type t = {
    view: view;
    mutable ty: Ty.t;
    mutable id: int;
  }
  and view =
    | Bool of bool
    | Not of t
    | Eq of t * t
    | App of Var.t * t list

  let view t = t.view
  let ty t = t.ty
  let equal a b = a.id=b.id
  let compare a b = CCInt.compare a.id b.id
  let hash a = CCHash.int a.id

  module H = Hashcons.Make(struct
      type nonrec t = t
      let equal a b = match view a, view b with
        | Bool a, Bool b -> a=b
        | Not a, Not b -> equal a b
        | Eq (a1,a2), Eq (b1,b2) -> equal a1 b1 && equal a2 b2
        | App (f1,l1), App (f2,l2) -> Var.equal f1 f2 && CCList.equal equal l1 l2
        | (Bool _ | Not _ | Eq _ | App _), _ -> false

      let hash t =
        let module H = CCHash in
        match view t with
        | Bool b -> H.combine2 10 (H.bool b)
        | Not a -> H.combine2 20 (hash a)
        | Eq (a,b) -> H.combine3 30 (hash a) (hash b)
        | App (f, l) -> H.combine3 40 (Var.hash f) (H.list hash l)

      let set_id t id = assert (t.id < 0); t.id <- id
    end)

  let rec pp out (t:t) : unit =
    match view t with
    | Bool b -> Fmt.bool out b
    | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" pp a pp b
    | Not a -> Fmt.fprintf out "(@[not@ %a@])" pp a
    | App (f, []) -> Var.pp out f
    | App (f, l) -> Fmt.fprintf out "(@[%a@ %a@])" Var.pp f (Util.pp_list pp) l

  let ty_of_view_ = function
    | Bool _ -> Ty.bool
    | Eq (a,b) ->
      if not (Ty.equal (ty a) (ty b)) then (
        Util.errorf "cannot equate %a@ and %a:@ incompatible types" pp a pp b;
      );
      Ty.bool
    | Not a ->
      if not (Ty.equal (ty a) Ty.bool) then (
        Util.errorf "@[cannot compute negation of non-boolean@ %a@]" pp a;
      );
      Ty.bool
    | App (f, l) ->
      let args, ret = Ty.open_ (Var.ty f) in
      if List.length args <> List.length l then (
        Util.errorf "@[incompatible arity:@ %a@ applied to %a@]" Var.pp f (Fmt.Dump.list pp) l;
      );
      begin 
        match CCList.find_opt (fun (t,ty_a) -> not @@ Ty.equal (ty t) ty_a) (List.combine l args)
        with
        | None -> ()
        | Some (t,ty_a) ->
          Util.errorf "@[argument %a@ should have type %a@]" pp t Ty.pp ty_a
      end;
      ret

  let mk_ : view -> t =
    let tbl = H.create ~size:256 () in
    fun view ->
      let t = {view; id= -1; ty=Ty.bool} in
      let u = H.hashcons tbl t in
      if t == u then u.ty <- ty_of_view_ view;
      u

  let bool b : t = mk_ (Bool b)
  let true_ = bool true
  let false_ = bool false
  let app f l : t = mk_ (App (f, l))
  let const f = app f []
  let eq a b : t =
    let view = if compare a b < 0 then Eq (a,b) else Eq(b,a) in
    mk_ view

  let not_ a = match view a with
    | Bool b -> bool (not b)
    | Not u -> u
    | _ -> mk_ (Not a)
  let neq a b = not_ @@ eq a b

  let abs t = match view t with
    | Bool false -> true_
    | Not u -> u
    | _ -> t

  module As_key = struct type nonrec t = t let compare=compare let equal=equal let hash=hash end

  module Set = CCSet.Make(As_key)
  module Map = CCMap.Make(As_key)
  module Tbl = CCHashtbl.Make(As_key)

  let parse (env:Env.t) : t P.t =
    let open P.Infix in
    P.fix (fun self ->
        let self' = P.try_ (self <* P.skip_white) in
        P.(try_ (string "true") *> return true_) <|>
        P.(try_ (string "false") *> return false_) <|>
        (P.try_ P.U.word >>= Var.parse_string env.Env.vars >|= const) <|>
        (P.try_ (P.char '(') *> P.skip_space *>
         ( (P.try_ (P.char '=') *> P.skip_white *>
            (self' >>= fun a -> self' <* P.skip_white <* P.char ')'
             >|= fun b -> eq a b)) <|>
           (P.try_ (P.string "not") *> P.skip_white *> (self' >|= not_)
            <* P.skip_white <* P.char ')') <|>
           (* apply *)
           (P.try_ P.U.word <* P.skip_white >>= Var.parse_string env.Env.vars
            >>= fun f -> P.many self' <* P.skip_white <* P.char ')'
            >|= fun l -> app f l)
         ) ) <?> "expected term"
      )
end

module Lit = Term

module Clause = struct
  type t = Lit.Set.t
  let pp out c =
    if Lit.Set.cardinal c = 1
    then Lit.pp out (Lit.Set.choose c)
    else Fmt.fprintf out "(@[or@ %a@])" (pp_list Lit.pp) (Lit.Set.to_list c)
  let is_empty = Lit.Set.is_empty
  let contains l c = Lit.Set.mem l c
  let remove l c : t = Lit.Set.remove l c
  let union = Lit.Set.union
  let lits c = Lit.Set.to_seq c
  let for_all = Lit.Set.for_all
  let filter = Lit.Set.filter
  let of_list = Lit.Set.of_list

  let as_unit c = match Lit.Set.choose_opt c with
    | None -> None
    | Some lit ->
      let c' = remove lit c in
      if is_empty c' then Some lit else None

  let parse (env:Env.t) : t P.t =
    let open P in
    skip_white *> parsing "clause" (
      (try_ (char '(' *> string "or") *> skip_white *>
       (many (try_ (Lit.parse env) <* skip_white) <* char ')' >|= Lit.Set.of_list)) <|>
      (Lit.parse env >|= Lit.Set.singleton)
    )
end

module Trail = struct
  type kind = Decision | Prop of Clause.t
  type t =
    | Nil
    | Cons of {
        kind: kind;
        lit: Lit.t;
        next: t;
        _assign: bool Lit.Map.t lazy_t; (* assignment, from trail *)
      }

  let[@inline] assign = function
    | Nil -> Lit.Map.empty
    | Cons {_assign=lazy a;_} -> a

  let empty = Nil
  let cons kind (lit:Lit.t) (next:t) : t =
    let _assign = lazy (
      let a = assign next in
      a |> Lit.Map.add lit true |> Lit.Map.add (Lit.not_ lit) false
    ) in
    Cons { kind; lit; next; _assign; }

  let eval_to_false (self:t) (c:Clause.t) : bool =
    let map = assign self in
    Clause.for_all (fun l -> Lit.Map.get_or ~default:false (Lit.not_ l) map) c

  let rec iter k = function
    | Nil -> ()
    | Cons {kind;lit;next;_} -> k (kind,lit); iter k next

  let to_iter (tr:t) = fun k -> iter k tr

  let pp_trail_elt out (k,lit) = match k with
    | Decision -> Fmt.fprintf out "%a*" Lit.pp lit
    | Prop _ -> Lit.pp out lit

  let pp out (self:t) : unit =
    Fmt.fprintf out "(@[%a@])" (pp_iter pp_trail_elt) (to_iter self)
end

module State = struct
  type status =
    | Sat
    | Unsat
    | Conflict of Clause.t
    | Backjump of Clause.t
    | Searching
  type t = {
    env: Env.t;
    cs: Clause.t list;
    trail: Trail.t;
    status: status;
    _all_vars: Lit.Set.t lazy_t;
    _to_decide: Lit.Set.t lazy_t;
  }

  (* main constructor *)
  let make (env:Env.t) (cs:Clause.t list) (trail:Trail.t) status : t =
    let _all_vars = lazy (
      Iter.(of_list cs |> flat_map Clause.lits |> map Lit.abs) |> Lit.Set.of_seq;
    ) in
    let _to_decide = lazy (
      let lazy all = _all_vars in
      let in_trail =
        Iter.(Trail.to_iter trail |> map snd |> map Lit.abs) |> Lit.Set.of_seq in
      Lit.Set.diff all in_trail
    ) in
    { env; cs; trail; status;
      _all_vars; _to_decide }

  let empty : t = make Env.empty [] Trail.empty Searching

  let pp_status out = function
    | Sat -> Fmt.string out "sat"
    | Unsat -> Fmt.string out "unsat"
    | Searching -> Fmt.string out "searching"
    | Conflict c -> Fmt.fprintf out "(@[conflict %a@])" Clause.pp c
    | Backjump c -> Fmt.fprintf out "(@[backjump %a@])" Clause.pp c

  let pp out (self:t) : unit =
    Fmt.fprintf out
      "(@[<hv>st @[:status@ %a@]@ @[:cs@ (@[<v>%a@])@]@ @[:trail@ %a@]@ @[<2>:env@ %a@]@])"
      pp_status self.status (pp_list Clause.pp) self.cs Trail.pp self.trail
      Env.pp self.env

  let parse_one (env:Env.t) (cs:Clause.t list) : (Env.t * Clause.t list) P.t =
    let open P in
    (* assert *)
    (try_ (char '(' *> skip_white *> string "assert") *> skip_white *>
     (parsing "assert" (Clause.parse env)
      >|= fun c -> (env,c::cs)) <* skip_white <* char ')') <|>
    (* new type *)
    (try_ (char '(' *> skip_white *> string "ty") *> skip_white *>
     parsing "ty"
       (U.word >|= fun ty -> Env.add_ty (ID.make ty) env, cs) <* skip_white <* char ')') <|>
    (* new function *)
    (try_ (char '(' *> skip_white *> string "fun") *> skip_white *>
     parsing "fun" (U.word >>= fun f ->
      (skip_white *> parsing "ty" (Ty.parse env.Env.ty) <* skip_white <* char ')') >|= fun ty ->
      let v = Var.make (ID.make f) ty in
      Env.add_var v env, cs))

  let rec parse_rec (env:Env.t) (cs:Clause.t list) : (Env.t * Clause.t list) P.t =
    let open P in
    skip_white *> (
      (* done *)
      (try_ (char ')') *> return (env, List.rev cs)) <|>
      (* one statement, then recurse *)
      (try_ (parsing "statement" @@ parse_one env cs)
       >>= fun (env,cs) -> parse_rec env cs)
    )

  let parse : t P.t =
    let open P in
    (skip_white *> char '(' *> parse_rec Env.empty [])
    >|= fun (env,cs) -> make env cs Trail.empty Searching

  let resolve_conflict_ (self:t) : _ ATS.step option =
    let open ATS in
    match self.status with
    | Conflict c when Clause.is_empty c ->
      Some (One (make self.env self.cs self.trail Unsat, "learnt false"))
    | Conflict c ->
      begin match self.trail with
        | Trail.Nil ->
          Some (One (make self.env self.cs self.trail Unsat, "empty trail")) (* unsat! *)
        | Trail.Cons {kind=Prop d;lit;next;_} when Clause.contains (Lit.not_ lit) c ->
          (* resolution *)
          assert (Clause.contains lit d);
          let res = Clause.union (Clause.remove lit d) (Clause.remove (Lit.not_ lit) c) in
          let expl = Fmt.sprintf "resolve on %a with %a" Lit.pp lit Clause.pp d in
          Some (One (make self.env self.cs next (Conflict res), expl))
        | Trail.Cons {kind=Prop _; next; _} ->
          Some (One (make self.env self.cs next self.status, "consume"))
        | Trail.Cons {kind=Decision; _} ->
          (* start backjumping *)
          Some (One (make self.env self.cs self.trail (Backjump c), "backjump below conflict level"))
      end
    | _ -> None

  (* TODO: instead of decision, use criterion about learnt clause becoming unit,
     and then unwind to decision and propagate *)
  let backjump_ (self:t) : _ ATS.step option =
    let open ATS in
    match self.status with
    | Backjump c when Clause.is_empty c ->
      Some (One (make self.env self.cs self.trail Unsat, "learnt false"))
    | Backjump c ->
      let rec unwind_trail trail =
        match trail with
        | Trail.Nil -> 
          Some (One (make self.env self.cs self.trail Unsat, "empty trail")) (* unsat! *)
        | Trail.Cons {lit; _}
          when Clause.contains (Lit.not_ lit) c
            && Trail.eval_to_false trail (Clause.remove (Lit.not_ lit) c) ->
          (* reached UIP *)
          let tr = unwind_till_next_decision trail in
          let expl = Fmt.sprintf "backjump with %a" Clause.pp c in
          let trail = Trail.cons (Prop c) (Lit.not_ lit) tr in
          Some (One (make self.env (c :: self.cs) trail Searching, expl))
        | Trail.Cons {next;_} -> unwind_trail next
      and unwind_till_next_decision = function
        | Trail.Nil -> Trail.empty
        | Trail.Cons {kind=Decision; next; _} -> next
        | Trail.Cons {kind=Prop _;next; _} -> unwind_till_next_decision next
      in
      unwind_trail self.trail
    | _ -> None

  let find_unit_c (self:t) : (Clause.t * Lit.t) option =
    let assign = Trail.assign self.trail in
    Iter.of_list self.cs
    |> Iter.find_map
      (fun c ->
         (* non-false lits *)
         let c' = Clause.filter (fun l -> Lit.Map.get l assign <> Some false) c in
         match Clause.as_unit c' with
         | Some l when not (Lit.Map.mem l assign) -> Some (c,l)
         | _ -> None)

  let propagate self : _ ATS.step option =
    match find_unit_c self with
    | Some (c,lit) ->
      let expl = Fmt.sprintf "propagate %a from %a" Lit.pp lit Clause.pp c in
      let trail = Trail.cons (Prop c) lit self.trail in
      Some (ATS.One (make self.env self.cs trail Searching, expl))
    | None -> None

  let decide self : _ ATS.step option =
    (* try to decide *)
    let lazy vars = self._to_decide in
    if Lit.Set.is_empty vars then (
      (* full model, we're done! *)
      Some (ATS.Done (make self.env self.cs self.trail Sat, "all vars decided"))
    ) else (
      (* multiple possible decisions *)
      let decs =
        Lit.Set.to_seq vars
        |> Iter.flat_map_l
          (fun v ->
             let mk_ v =
               make self.env self.cs (Trail.cons Decision v self.trail) Searching,
               Fmt.sprintf "decide %a" Lit.pp v
             in
             [mk_ v; mk_ (Lit.not_ v)])
        |> Iter.to_rev_list
      in
      Some (ATS.Choice decs)
    )

  let find_false (self:t) : _ option =
    match CCList.find_opt (Trail.eval_to_false self.trail) self.cs with
    | None -> None
    | Some c ->
      (* conflict! *)
      Some (ATS.One (make self.env self.cs self.trail (Conflict c), "false clause"))

  let is_done (self:t) =
    match self.status with
    | Sat | Unsat -> Some (ATS.Done (self, "done"))
    | _ -> None

  let rules : _ ATS.rule list list = [
    [is_done];
    [resolve_conflict_; backjump_];
    [find_false];
    [propagate];
    [decide];
  ]
end

module A = struct
  let name = "mcsat"
  module State = State
  let rules = State.rules
end

let ats : ATS.t = (module ATS.Make(A))
