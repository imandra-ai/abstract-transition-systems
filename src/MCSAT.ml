open Util

(* scoping table *)
let scope_ : ID.t Str_tbl.t = Str_tbl.create 24

module Ty : sig
  type t = Bool | Rat | Unin of ID.t
  val equal : t -> t -> bool
  val hash : t -> int
  val bool : t
  val rat : t
  val unin : ID.t -> t
  val pp : t Fmt.printer
val parse : t P.t
end = struct
  type t = Bool | Rat | Unin of ID.t
  let equal a b = match a, b with
    | Bool, Bool
    | Rat, Rat -> true
    | Unin a, Unin b -> ID.equal a b
    | (Bool | Rat | Unin _), _ -> false
  let hash = function
    | Bool -> 1
    | Rat -> 2
    | Unin id -> CCHash.combine2 10 (ID.hash id)
  let bool = Bool
  let rat = Rat
  let unin id = Unin id
  let pp out = function
    | Bool -> Fmt.string out "bool"
    | Rat -> Fmt.string out "rat"
    | Unin id -> ID.pp out id
  let parse =
    let open P in
    skip_white *> (
      (try_ (string "bool") *> return bool) <|>
      (try_ (string "rat") *> return rat) <|>
      (try_ U.word >>= fun s ->
       (try return (unin (Str_tbl.find scope_ s))
        with Not_found -> failf "not in scope: type %S" s)))
end

module Var : sig

end = struct

  end

module Term : sig
  type t
  type view =
    | Bool of bool
    | Not of t
    | Eq of t * t
    | App of ID.t * t list

  val view : t -> view
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int

  val bool : bool -> t
  val true_ : t
  val false_ : t
  val const : ID.t -> t
  val app : ID.t -> t list -> t
  val eq : t -> t -> t
  val neq : t -> t -> t
  val not_ : t -> t
  val abs : t -> t

  val pp : t Fmt.printer

  val parse : t P.t

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t
end = struct
  type t = {
    view: view;
    mutable id: int;
  }
  and view =
    | Bool of bool
    | Not of t
    | Eq of t * t
    | App of ID.t * t list

  let view t = t.view
  let equal a b = a.id=b.id
  let compare a b = CCInt.compare a.id b.id
  let hash a = CCHash.int a.id

  module H = Hashcons.Make(struct
      type nonrec t = t
      let equal a b = match view a, view b with
        | Bool a, Bool b -> a=b
        | Not a, Not b -> equal a b
        | Eq (a1,a2), Eq (b1,b2) -> equal a1 b1 && equal a2 b2
        | App (f1,l1), App (f2,l2) -> ID.equal f1 f2 && CCList.equal equal l1 l2
        | (Bool _ | Not _ | Eq _ | App _), _ -> false

      let hash t =
        let module H = CCHash in
        match view t with
        | Bool b -> H.combine2 10 (H.bool b)
        | Not a -> H.combine2 20 (hash a)
        | Eq (a,b) -> H.combine3 30 (hash a) (hash b)
        | App (f, l) -> H.combine3 40 (ID.hash f) (H.list hash l)

      let set_id t id = assert (t.id < 0); t.id <- id
      end)

  let mk_ : view -> t =
    let tbl = H.create ~size:256 () in
    fun view ->
      let t = {view; id= -1} in
      H.hashcons tbl t

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

  let rec pp out (t:t) : unit =
    match view t with
    | Bool b -> Fmt.bool out b
    | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" pp a pp b
    | Not a -> Fmt.fprintf out "(@[not@ %a@])" pp a
    | App (id, []) -> ID.pp out id
    | App (id, l) -> Fmt.fprintf out "(@[%a@ %a@])" ID.pp id (Util.pp_list pp) l

  module As_key = struct type nonrec t = t let compare=compare let equal=equal let hash=hash end

  module Set = CCSet.Make(As_key)
  module Map = CCMap.Make(As_key)
  module Tbl = CCHashtbl.Make(As_key)

  (* TODO: parser *)
  let parse _ = assert false
end

module Lit = Term

module Clause = struct
  type t = Lit.Set.t
  let pp out c = Fmt.fprintf out "(@[%a@])" (pp_list Lit.pp) (Lit.Set.to_list c)
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

  let parse : t P.t =
    let open P in
    parsing "clause"
      ((skip_white *> char '(' *> many (try_ Lit.parse) >|= Lit.Set.of_list)
       <* skip_white <* char ')')
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
    cs: Clause.t list;
    trail: Trail.t;
    status: status;
    _all_vars: Lit.Set.t lazy_t;
    _to_decide: Lit.Set.t lazy_t;
  }

  (* main constructor *)
  let make (cs:Clause.t list) (trail:Trail.t) status : t =
    let _all_vars = lazy (
      Iter.(of_list cs |> flat_map Clause.lits |> map Lit.abs) |> Lit.Set.of_seq;
    ) in
    let _to_decide = lazy (
      let lazy all = _all_vars in
      let in_trail =
        Iter.(Trail.to_iter trail |> map snd |> map Lit.abs) |> Lit.Set.of_seq in
      Lit.Set.diff all in_trail
    ) in
    {cs; trail; status; _all_vars; _to_decide }

  let empty : t = make [] Trail.empty Searching

  let pp_status out = function
    | Sat -> Fmt.string out "sat"
    | Unsat -> Fmt.string out "unsat"
    | Searching -> Fmt.string out "searching"
    | Conflict c -> Fmt.fprintf out "(@[conflict %a@])" Clause.pp c
    | Backjump c -> Fmt.fprintf out "(@[backjump %a@])" Clause.pp c

  let pp out (self:t) : unit =
    Fmt.fprintf out
      "(@[st @[:status@ %a@]@ @[:cs@ (@[%a@])@]@ @[:trail@ %a@]@])"
      pp_status self.status (pp_list Clause.pp) self.cs Trail.pp self.trail

  let parse : t P.t =
    let open P in
    (skip_white *> char '(' *>
     parsing "clause list" (many Clause.parse <* skip_white) <* char ')')
    >|= fun cs -> make cs Trail.empty Searching

  let resolve_conflict_ (self:t) : _ ATS.step option =
    let open ATS in
    match self.status with
    | Conflict c when Clause.is_empty c ->
      Some (One (make self.cs self.trail Unsat, "learnt false"))
    | Conflict c ->
      begin match self.trail with
        | Trail.Nil ->
          Some (One (make self.cs self.trail Unsat, "empty trail")) (* unsat! *)
        | Trail.Cons {kind=Prop d;lit;next;_} when Clause.contains (Lit.not_ lit) c ->
          (* resolution *)
          assert (Clause.contains lit d);
          let res = Clause.union (Clause.remove lit d) (Clause.remove (Lit.not_ lit) c) in
          let expl = Fmt.sprintf "resolve on %a with %a" Lit.pp lit Clause.pp d in
          Some (One (make self.cs next (Conflict res), expl))
        | Trail.Cons {kind=Prop _; next; _} ->
          Some (One (make self.cs next self.status, "consume"))
        | Trail.Cons {kind=Decision; _} ->
          (* start backjumping *)
          Some (One (make self.cs self.trail (Backjump c), "backjump below conflict level"))
      end
    | _ -> None

  (* TODO: instead of decision, use criterion about learnt clause becoming unit,
     and then unwind to decision and propagate *)
  let backjump_ (self:t) : _ ATS.step option =
    let open ATS in
    match self.status with
    | Backjump c when Clause.is_empty c ->
      Some (One (make self.cs self.trail Unsat, "learnt false"))
    | Backjump c ->
      let rec unwind_trail trail =
        match trail with
        | Trail.Nil -> 
          Some (One (make self.cs self.trail Unsat, "empty trail")) (* unsat! *)
        | Trail.Cons {lit; _}
          when Clause.contains (Lit.not_ lit) c
            && Trail.eval_to_false trail (Clause.remove (Lit.not_ lit) c) ->
          (* reached UIP *)
          let tr = unwind_till_next_decision trail in
          let expl = Fmt.sprintf "backjump with %a" Clause.pp c in
          let trail = Trail.cons (Prop c) (Lit.not_ lit) tr in
          Some (One (make (c :: self.cs) trail Searching, expl))
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
      Some (ATS.One (make self.cs trail Searching, expl))
    | None -> None

  let decide self : _ ATS.step option =
    (* try to decide *)
    let lazy vars = self._to_decide in
    if Lit.Set.is_empty vars then (
      (* full model, we're done! *)
      Some (ATS.Done (make self.cs self.trail Sat, "all vars decided"))
    ) else (
      (* multiple possible decisions *)
      let decs =
        Lit.Set.to_seq vars
        |> Iter.flat_map_l
          (fun v ->
             let mk_ v =
               make self.cs (Trail.cons Decision v self.trail) Searching,
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
      Some (ATS.One (make self.cs self.trail (Conflict c), "false clause"))

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
