open Util

(** {2 Types} *)
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

  val is_bool : t -> bool

  type env = t Str_map.t
  val parse : env -> t P.t

  module Tbl : CCHashtbl.S with type key = t
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

  let is_bool ty = match view ty with Bool -> true | _ -> false

  let rec pp out t = match view t with
    | Bool -> Fmt.string out "bool"
    | Rat -> Fmt.string out "rat"
    | Unin id -> ID.pp out id
    | Arrow (a,b) -> Fmt.fprintf out "(@[->@ %a@ %a@])" pp a pp b

  type env = t Str_map.t
  let parse env : t P.t =
    let open P.Infix in
    P.fix (fun self ->
        P.match_
          ~atom:(P.string >>= function
            | "bool" -> P.return bool
            | "rat" -> P.return rat
            | s ->
              begin match Str_map.get s env with
                | Some ty -> P.return ty
                | None -> P.failf "not in scope: type %S" s
              end)
          ~list:(P.parsing "ty" @@ P.uncons P.string (function
              | "->" ->
                P.list self >>= fun args ->
                begin match List.rev args with
                  | [] | [_] -> P.fail "-> needs at least 2 arguments"
                  | ret :: args -> P.return (arrow_l (List.rev args) ret)
                end
              | s -> P.failf "unknown type constructor %S" s
            )))

  module As_key = struct type nonrec t = t let compare=compare let equal=equal let hash=hash end
  module Tbl = CCHashtbl.Make(As_key)
end

(** {2 Typed Constants} *)
module Var : sig
  type t = {id: ID.t; ty: Ty.t}
  val make : ID.t -> Ty.t -> t
  val id : t -> ID.t
  val name : t -> string
  val ty : t -> Ty.t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val pp : t Fmt.printer

  type env = t Str_map.t
  val parse : env -> t P.t
  val parse_string : env -> string -> t P.t
  module Map : CCMap.S with type key = t
  module Set : CCSet.S with type elt = t
end = struct
  type t = {id: ID.t; ty: Ty.t}
  let id v = v.id
  let ty v = v.ty
  let name v = ID.name @@ id v
  let make id ty : t = {id; ty}
  let equal a b = ID.equal a.id b.id
  let compare a b = ID.compare a.id b.id
  let hash a = ID.hash a.id
  let pp out a = ID.pp out a.id

  type env = t Str_map.t
  let parse_string env s =
    try P.return (Str_map.find s env)
    with Not_found -> P.failf "not in scope: variable %S" s
  let parse env : t P.t =
    let open P.Infix in
    P.string >>= parse_string env

  module As_key = struct type nonrec t = t let compare=compare let equal=equal let hash=hash end
  module Map = CCMap.Make(As_key)
  module Set = CCSet.Make(As_key)
end

(** {2 Semantic Values} *)
module Value : sig
  type t = Bool of bool | Unin of Var.t

  val ty : t -> Ty.t
  val pp : t Fmt.printer

  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
  val ty : t -> Ty.t

  val is_bool : t -> bool
  val bool : bool -> t
  val not_ : t -> t
  val true_ : t
  val false_ : t
  val unin_var : Var.t -> t
  val unin : Ty.t -> int -> t (* from counter + type *)
end = struct
  type t =  Bool of bool | Unin of Var.t

  let ty = function Bool _ -> Ty.bool | Unin v -> Var.ty v
  let pp out = function
    | Bool b -> Fmt.bool out b
    | Unin v -> Var.pp out v

  let bool b = Bool b
  let true_ = bool true
  let false_ = bool false
  let unin_var v : t = Unin v
  let is_bool = function Bool _ -> true | _ -> false
  let equal a b = match a, b with
    | Bool a, Bool b -> a=b
    | Unin a, Unin b -> Var.equal a b
    | (Bool _ | Unin _), _ -> false
  let compare a b =
    let to_int_ = function Bool _ -> 1 | Unin _ -> 2 in
    match a, b with
    | Bool a, Bool b -> CCBool.compare a b
    | Unin a, Unin b -> Var.compare a b
    | (Bool _ | Unin _), _ -> CCInt.compare (to_int_ a) (to_int_ b)
  let hash = function
    | Bool b -> CCHash.(combine2 10 (bool b))
    | Unin v -> CCHash.(combine2 20 (Var.hash v))

  let not_ = function
    | Bool b -> bool (not b)
    | v -> Util.errorf "cannot negate value %a" pp v

  let unin =
    let tbl : t list Ty.Tbl.t = Ty.Tbl.create 32 in
    fun ty i ->
      let l = Ty.Tbl.get_or ~default:[] tbl ty in
      let len_l = List.length l in
      let n_missing = i - len_l in
      if n_missing < 0 then (
        List.nth l i
      ) else (
        (* extend list *)
        let extend =
          CCList.init (n_missing+1)
            (fun i -> unin_var @@ Var.make (ID.makef "$%a_%d" Ty.pp ty (i+len_l)) ty)
        in
        let l = l @ extend in
        Ty.Tbl.replace tbl ty l;
        List.nth l i
      )
end

module Env = struct
  type t = {
    ty: Ty.env;
    vars: Var.env;
  }

  let empty : t = {ty=Str_map.empty; vars=Str_map.empty; }
  let length env = Str_map.cardinal env.ty + Str_map.cardinal env.vars

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

  let pp_item out = function
    | Ty id -> Fmt.fprintf out "(@[<2>ty@ %a@])" Ty.pp id
    | Fun v -> Fmt.fprintf out "(@[<2>fun@ %a@ %a@])" Var.pp v Ty.pp (Var.ty v)

  let pp out (self:t) =
    Fmt.fprintf out "(@[<hv>%a@])" (Util.pp_iter pp_item) (to_iter self)
end

(** {2 Terms} *)
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
  val weight : t -> int

  val bool : bool -> t
  val true_ : t
  val false_ : t
  val const : Var.t -> t
  val app : Var.t -> t list -> t
  val eq : t -> t -> t
  val neq : t -> t -> t
  val not_ : t -> t
  val abs : t -> t
  val sign : t -> bool

  val sub : t -> t Iter.t
  val is_bool : t -> bool (** Has boolean type? *)

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
    mutable weight: int;
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
  let weight t = t.weight

  let is_bool t = Ty.is_bool (ty t)

  let sub t k =
    let rec aux t =
      k t;
      match view t with
      | Bool _ | App (_, []) -> ()
      | App (_, l) -> List.iter aux l
      | Eq (a,b) -> aux a; aux b
      | Not u -> aux u
    in aux t

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

  let weight_of_view_ = function
    | Bool _ -> 1
    | Eq (a,b) -> 1 + weight a + weight b
    | Not a -> 1 + weight a
    | App (_f, l) -> List.fold_left (fun n t -> n+ weight t) 1 l

  let mk_ : view -> t =
    let tbl = H.create ~size:256 () in
    fun view ->
      let t = {view; id= -1; ty=Ty.bool; weight= -1;} in
      let u = H.hashcons tbl t in
      if t == u then (
        u.ty <- ty_of_view_ view;
        u.weight <- weight_of_view_ view;
      );
      u

  let bool b : t = mk_ (Bool b)
  let true_ = bool true
  let false_ = bool false
  let app f l : t = mk_ (App (f, l))
  let const f = app f []
  let eq a b : t =
    if equal a b then true_
    else (
      let view = if compare a b < 0 then Eq (a,b) else Eq(b,a) in
      mk_ view
    )

  let not_ a = match view a with
    | Bool b -> bool (not b)
    | Not u -> u
    | _ -> mk_ (Not a)

  let neq a b = not_ @@ eq a b

  let abs t = match view t with
    | Bool false -> true_
    | Not u -> u
    | _ -> t

  let sign t = match view t with
    | Bool b -> b
    | Not _ -> false
    | _ -> true

  module As_key = struct type nonrec t = t let compare=compare let equal=equal let hash=hash end

  module Set = CCSet.Make(As_key)
  module Map = CCMap.Make(As_key)
  module Tbl = CCHashtbl.Make(As_key)

  let parse (env:Env.t) : t P.t =
    let open P.Infix in
    P.fix (fun self ->
        P.match_
          ~atom:(P.string >>= function
          | "true" -> P.return true_
          | "false" -> P.return false_
          | s ->
            Var.parse_string env.Env.vars s >|= const)
          ~list:(P.parsing "expr" @@ P.uncons P.string (function
              | "=" -> P.parsing "equality" (P.list2 self self) >|= fun (a,b) -> eq a b
              | "not" -> P.parsing "negation" (P.list1 self) >|= not_
              | s ->
                Var.parse_string env.Env.vars s >>= fun f ->
                P.list self >|= fun l ->
                app f l
            )))
end

(** Precedence on symbols *)
module Precedence : sig
  type t
  val empty : t
  val compare : t -> Var.t -> Var.t -> int

  val to_iter : t -> Var.t Iter.t
  val to_list : t -> Var.t list
  val pp : t Fmt.printer
  val to_string : t -> string

  val complete : Var.t list -> Var.env -> t
  (** [complete l1 env] makes a precedence where elements of [l1] are
      the smallest ones (in that order), and remaining elements of [env] are bigger
      than elements of [l1] but in some unspecified order. *)
end = struct
  type t = {
    l: Var.t list;
    m: int Var.Map.t lazy_t;
  }

  let mk_ (l:_ list) : t =
    let m = lazy (
      CCList.foldi (fun m i v -> Var.Map.add v i m) Var.Map.empty l
      ) in
    {l; m}

  let empty : t = mk_ []

  let to_list self = self.l
  let to_iter self = CCList.to_seq self.l

  let pp out (self:t) =
    Fmt.fprintf out "(@[%a@])" (Util.pp_iter ~sep:"<" Var.pp) (to_iter self)
  let to_string = Fmt.to_string pp

  let compare (self:t) v1 v2 : int =
    let lazy m = self.m in
    try CCInt.compare (Var.Map.find v1 m) (Var.Map.find v2 m)
    with Not_found -> Util.errorf "precedence.compare %a, %a@ for %a" Var.pp v1 Var.pp v2 pp self

  let complete l1 env : t =
    (* find values of [env] not in [l1] *)
    let l2 =
      Var.Set.diff (Var.Set.of_seq @@ Str_map.values env) (Var.Set.of_list l1)
      |> Var.Set.to_list
    in
    let l = l1 @ l2 in
    mk_ l
end

module KBO : sig
  val compare : prec:Precedence.t -> Term.t -> Term.t -> int
end = struct
  let rec compare ~prec t1 t2 : int =
    let self = compare ~prec in
    if Term.equal t1 t2 then 0
    else if Term.weight t1 > Term.weight t2 then 1
    else if Term.weight t1 < Term.weight t2 then -1
    else (
      match Term.view t1, Term.view t2 with
      | Bool b1, Bool b2 -> CCBool.compare b1 b2
      | Bool _, _ -> -1
      | _, Bool _ -> 1
      | Eq (a1,b1), Eq (a2,b2) ->
        if Term.equal a1 a2 then self b1 b2 else (
          let r = self a1 a2 in
          assert (r <> 0);
          r
        )
      | Eq _, _ -> -1
      | _, Eq _ -> 1
      | Not a, Not b -> self a b
      | Not _, _ -> -1
      | _, Not _ -> 1
      | App (f1, l1), App (f2,l2) ->
        begin match Precedence.compare prec f1 f2 with
          | 0 ->
            assert (Var.equal f1 f2);
            assert (List.length l1 = List.length l2);
            CCList.compare self l1 l2
          | n -> n
        end
    )
end

module SigMap = CCMap.Make(struct
    type t = Var.t * Value.t list
    let compare (f1,l1) (f2,l2) =
      if Var.equal f1 f2 then CCList.compare Value.compare l1 l2
      else Var.compare f1 f2
  end)

module Op : sig
  type t =
    | Rewrite of {l: Term.t; r: Term.t; }
    | Assign of {t: Term.t; value: Value.t; } 

  val lhs : t -> Term.t
  val pp : t Fmt.printer
end = struct
  type t =
    | Rewrite of {l: Term.t; r: Term.t; }
    | Assign of {t: Term.t; value: Value.t; } 

  let[@inline] lhs = function
    | Rewrite {l;_} -> l
    | Assign {t;_} -> t

  let pp out = function
    | Assign {t; value} -> Fmt.fprintf out "(@[<2>%a@ <- %a@])" Term.pp t Value.pp value
    | Rewrite {l;r} -> Fmt.fprintf out "(@[<2>%a@ --> %a@])" Term.pp l Term.pp r
end

module Assignment : sig
  type t

  type op = Op.t =
    | Rewrite of {l: Term.t; r: Term.t; }
    | Assign of {t: Term.t; value: Value.t; } 

  val normalize : t -> Term.t -> Term.t
  val evaluate : t -> Term.t -> Value.t option
  val evaluate_exn : t -> Term.t -> Value.t
  val does_evaluate : t -> Term.t -> bool

  val empty : t
  val add_rw : Term.t -> Term.t -> t -> t
  val add_assign : Term.t -> Value.t -> t -> t
  val add_op : op -> t -> t

  val to_iter : t -> op Iter.t
  val length : t -> int

  val pp : t Fmt.printer
end = struct
  module TM = Term.Map
  type t = {
    rw: Term.t TM.t;
    assign: Value.t TM.t;
  }

  let empty : t = { rw=TM.empty; assign=TM.empty; }

  type op = Op.t =
    | Rewrite of {l: Term.t; r: Term.t; }
    | Assign of {t: Term.t; value: Value.t; } 

  let to_iter self =
    let l1 = TM.to_seq self.rw |> Iter.map (fun (l,r) -> Rewrite {l;r}) in
    let l2 = TM.to_seq self.assign |> Iter.map (fun (t,value) -> Assign {t;value}) in
    Iter.append l1 l2

  let pp out self =
    Fmt.fprintf out "(@[<hv>%a@])" (Util.pp_iter Op.pp) (to_iter self)

  let add_rw l r self : t = {self with rw=TM.add l r self.rw}

  let add_assign t value self : t =
    let assign =
      if Value.is_bool value then (
        self.assign |> Term.Map.add t value
        |> Term.Map.add (Term.not_ t) (Value.not_ value)
      ) else (
        self.assign |> Term.Map.add t value
      )
    in
    {self with assign}

  let add_op op self : t = match op with
    | Assign {t; value} -> add_assign t value self
    | Rewrite {l; r} -> add_rw l r self

  let length self = TM.cardinal self.rw + TM.cardinal self.assign

  let rec normalize (self:t) (t:Term.t) =
    match TM.find t self.rw with
    | exception Not_found -> t
    | u -> normalize self u

  let evaluate (self:t) (t:Term.t) : _ option =
    let t = normalize self t in
    TM.get t self.assign

  let does_evaluate self t = CCOpt.is_some (evaluate self t)
  let evaluate_exn self t = match evaluate self t with
    | Some x -> x
    | None -> Util.errorf "evaluate_exn %a@ in %a" Term.pp t pp self
end

(** {2 Disjunction of boolean terms} *)
module Clause = struct
  type t = Term.Set.t
  let pp out c =
    if Term.Set.is_empty c then Fmt.string out "⊥"
    else if Term.Set.cardinal c = 1 then Term.pp out (Term.Set.choose c)
    else Fmt.fprintf out "(@[<hv>or@ %a@])" (pp_list Term.pp) (Term.Set.to_list c)
  let is_empty = Term.Set.is_empty
  let choose = Term.Set.choose
  let contains l c = Term.Set.mem l c
  let length = Term.Set.cardinal
  let remove l c : t = Term.Set.remove l c
  let union = Term.Set.union
  let lits c = Term.Set.to_seq c
  let for_all = Term.Set.for_all
  let filter = Term.Set.filter
  let of_list = Term.Set.of_list

  let as_unit c = match Term.Set.choose_opt c with
    | None -> None
    | Some lit ->
      let c' = remove lit c in
      if is_empty c' then Some lit else None

  let parse (env:Env.t) : t P.t =
    let open P in
    parsing "clause"
      (one_of [
          ("single-term", Term.parse env >|= Term.Set.singleton);
          ("or", uncons string
             (function
               | "or" -> list (Term.parse env) >|= Term.Set.of_list
               | s -> failf "expected `or`, not %S" s));
        ])

  (* semantic evaluation *)
  let rec eval_lit_semantic (ass:Assignment.t) (t:Term.t) : bool option =
    match Term.view t with
    | Term.Eq (a,b) ->
      begin match Assignment.evaluate ass a, Assignment.evaluate ass b with
        | Some va, Some vb -> Some (Value.equal va vb)
        | _ -> None
      end
    | Term.Not u ->
      CCOpt.map not (eval_lit_semantic ass u)
    | _ -> None

  (* semantic + trail evaluation *)
  let eval_lit (ass:Assignment.t) (t:Term.t) : bool option =
    match Assignment.evaluate ass t with
    | Some (Value.Bool b) -> Some b
    | Some _ -> assert false
    | None -> eval_lit_semantic ass t

  (* can [t] eval to false? *)
  let lit_eval_to_false (ass:Assignment.t) (t:Term.t) : bool =
    match Assignment.evaluate ass t, eval_lit_semantic ass t with
    | Some (Value.Bool false), _ | _, Some false -> true
    | _ -> false

  (* remove all literals that somehow evaluate to false *)
  let filter_false (ass:Assignment.t) (c:t) : t =
    filter
      (fun t -> not (lit_eval_to_false ass t))
      c

  let eval_to_false (ass:Assignment.t) (c:t) : bool =
    for_all (fun t -> lit_eval_to_false ass t) c

  module Set = CCSet.Make(struct type nonrec t = t let compare=compare end)
end

module Trail = struct
  type kind = Decision | BCP of Clause.t | Eval
  type op = Assignment.op =
    | Rewrite of { l: Term.t; r: Term.t; }
    | Assign of { t: Term.t; value: Value.t; }
  type t =
    | Nil
    | Cons of {
        kind: kind;
        op: op;
        next: t;
        level: int;
        _assign: Assignment.t lazy_t; (* assignment from this trail *)
        _prec: Precedence.t lazy_t;
        _assigned_vars: Var.t list; (* subset of unit variables assigned so far, top to bottom *)
      }

  let[@inline] assign = function
    | Nil -> Assignment.empty
    | Cons {_assign=lazy a;_} -> a

  let[@inline] level = function
    | Nil -> 0
    | Cons {level=l;_} -> l

  let assigned_vars = function
    | Nil -> []
    | Cons {_assigned_vars=a; _} -> a

  let cons ~env kind (op:op) (next:t) : t =
    (* Format.printf "trail.cons %a <- %a@." Term.pp lit Value.pp value; *)
    let level = match kind with
      | Decision -> 1 + level next
      | BCP _ | Eval -> level next
    and _assign = lazy (
      let a = assign next in
      Assignment.add_op op a
    )
    and _assigned_vars =
      let l = assigned_vars next in
      match Term.view (Op.lhs op) with
        | App (f, []) -> f :: l
        | _ -> l
    in
    let _prec = lazy (
      Precedence.complete (List.rev _assigned_vars) env.Env.vars
    ) in
    Cons { kind; op; next; _assign; _prec; level; _assigned_vars; }

  let cons_assign ~env kind (t:Term.t) (value:Value.t) next : t =
    let t, value =
      if Term.sign t then t, value else Term.not_ t, Value.not_ value in
    cons ~env kind (Assign {t; value}) next

  let cons_rw ~env kind (l:Term.t) (r:Term.t) next : t =
    cons ~env kind (Rewrite {l;r}) next

  let unit_true = Clause.of_list [Term.true_] (* axiom: [true] *)
  let empty = cons_assign (BCP unit_true) Term.true_ Value.true_ Nil

  let rec iter k = function
    | Nil -> ()
    | Cons {kind;op;next;level;_} ->
      k (kind, level, op);
      iter k next

  let to_iter (tr:t) : (kind * int * op) Iter.t = fun k -> iter k tr
  let iter_terms (tr:t) : Term.t Iter.t =
    to_iter tr |> Iter.map (fun (_,_,op) -> Op.lhs op)
  let iter_op (tr:t) : op Iter.t = to_iter tr |> Iter.map (fun (_,_,op) -> op)
  let length tr = to_iter tr |> Iter.length

  let pp_trail_elt out (k,level,op) =
    let cause = match k with Decision -> "*" | BCP _ -> "" | Eval -> "$" in
    Fmt.fprintf out "@[<h>[%d%s]%a@]" level cause Op.pp op

  let pp out (self:t) : unit =
    Fmt.fprintf out "(@[<v>%a@])" (pp_iter pp_trail_elt) (to_iter self)
end

module State = struct
  type conflict_uf =
    | CUF_forbid of {
        t: Term.t;
        v: Value.t;
        lit_force: Term.t;
        lit_forbid: Term.t;
      }
    | CUF_forced2 of {
        t: Term.t;
        v1: Value.t;
        v2: Value.t;
        lit_v1: Term.t;
        lit_v2: Term.t;
      }
    | CUF_congruence of {
        f: Var.t;
        t1: Term.t;
        t2: Term.t;
      }

  type status =
    | Sat
    | Unsat
    | Conflict_bool of Clause.t
    | Conflict_uf of conflict_uf
    | Searching

  type uf_domain =
    | UFD_forced of Value.t * Term.t
    | UFD_forbid of (Value.t * Term.t) list
    | UFD_conflict_forbid of Value.t * Term.t * Term.t
    | UFD_conflict_forced2 of Value.t * Term.t  * Value.t * Term.t 

  type t = {
    env: Env.t;
    cs: Clause.Set.t;
    trail: Trail.t;
    status: status;
    _all_vars: Term.Set.t lazy_t;
    _to_decide: Term.Set.t lazy_t;
    _uf_domain: uf_domain Term.Map.t lazy_t; (* incompatibility table for UF *)
    _uf_sigs: (Value.t * Term.t) SigMap.t lazy_t; (* signature table for UF *)
  }

  let[@inline] all_vars self = Lazy.force self._all_vars
  let[@inline] to_decide self = Lazy.force self._to_decide
  let[@inline] uf_domain self = Lazy.force self._uf_domain
  let[@inline] uf_sigs self = Lazy.force self._uf_sigs

  let view st = st.status, st.cs, st.trail, st.env

  (* compute domains, by looking for [a=b <- false]
     where [a] has a value already but [b] doesn't,
     or for [a=b <- true] where [a] has a value but [b] doesn't.
     We might detect conflicts when doing that. *)
  let compute_uf_domain trail : uf_domain Term.Map.t =
    let ass = Trail.assign trail in
    let is_ass x = Assignment.does_evaluate ass x in
    (* pairs of impossible assignments *)
    let pairs : (Term.t * Term.t * _) list =
      Trail.iter_op trail
      |> Iter.filter_map
        (function
          | Trail.Rewrite _ -> None
          | Trail.Assign {t; value} ->
            begin match Term.view t, value with
              | Term.Eq (a,b), Value.Bool bool when is_ass a && not (is_ass b) ->
                let value = Assignment.evaluate_exn ass a in
                Some (t, b, if bool then `Forced value else `Forbid value)
              | Term.Eq (a,b), Value.Bool bool when is_ass b && not (is_ass a) ->
                let value = Assignment.evaluate_exn ass b in
                Some (t, a, if bool then `Forced value else `Forbid value)
              | _ -> None
            end)
      |> Iter.to_rev_list
    in
    List.fold_left
      (fun m (t1,t,op) ->
         match op, Term.Map.get t m with
         | _, Some (UFD_conflict_forbid _ | UFD_conflict_forced2 _) -> m
         | `Forced v1, Some (UFD_forced (v2,t2)) ->
           if Value.equal v1 v2 then m
           else Term.Map.add t (UFD_conflict_forced2 (v1,t1,v2,t2)) m
         | `Forced v1, Some (UFD_forbid l) ->
           begin match CCList.find_opt (fun (v2,_) -> Value.equal v1 v2) l with
             | Some (_,t2) ->
               Term.Map.add t (UFD_conflict_forbid (v1,t1,t2)) m
             | None ->
               Term.Map.add t (UFD_forced (v1,t1)) m
           end
         | `Forbid v1, Some (UFD_forced (v2,t2)) ->
           if Value.equal v1 v2
           then Term.Map.add t (UFD_conflict_forbid (v1,t2,t1)) m
           else m
         | `Forbid v1, Some (UFD_forbid l) ->
           Term.Map.add t (UFD_forbid ((v1,t1)::l)) m
         | `Forced v1, None ->
           Term.Map.add t (UFD_forced (v1,t1)) m
         | `Forbid v1, None ->
           Term.Map.add t (UFD_forbid [v1,t1]) m)
      Term.Map.empty pairs

  (* compute signatures, by looking at terms [f t1…tn <- v] where each [t_i]
     also has a value *)
  let compute_uf_sigs trail =
    let ass = Trail.assign trail in
    let is_ass x = Assignment.does_evaluate ass x in
    Trail.iter_op trail
    |> Iter.filter_map
      (function
        | Trail.Rewrite {l=t;r} ->
          begin match Term.view t, Assignment.evaluate ass r with
            | Term.App (f, l), Some v when List.for_all is_ass l ->
              Some ((f, List.map (Assignment.evaluate_exn ass) l), (v,t))
            | _ -> None
          end
        | Trail.Assign {t; value=v} ->
          begin match Term.view t with
            | Term.App (f, l) when List.for_all is_ass l ->
              Some ((f, List.map (Assignment.evaluate_exn ass) l), (v,t))
            | _ -> None
          end)
    |> SigMap.of_seq

  (* main constructor *)
  let make (env:Env.t) (cs:Clause.Set.t) (trail:Trail.t) status : t =
    let _all_vars = lazy (
      Iter.(
        Clause.Set.to_seq cs
        |> flat_map Clause.lits |> flat_map Term.sub |> map Term.abs)
      |> Term.Set.of_seq;
    ) in
    let _to_decide = lazy (
      let lazy all = _all_vars in
      let in_trail =
        Iter.(Trail.iter_terms trail |> map Term.abs) |> Term.Set.of_seq in
      Term.Set.diff all in_trail
    ) in
    let _uf_sigs = lazy (compute_uf_sigs trail) in
    let _uf_domain = lazy (compute_uf_domain trail) in
    { env; cs; trail; status; _all_vars; _to_decide; _uf_sigs; _uf_domain; }

  let empty : t =
    make Env.empty Clause.Set.empty (Trail.empty ~env:Env.empty) Searching

  let pp_conflict_uf out = function
    | CUF_forbid {t;v;lit_force;lit_forbid} ->
      Fmt.fprintf out "(@[conflict-uf-forbid@ @[%a <-@ %a@]@ :force %a@ :forbid %a@])"
        Term.pp t Value.pp v Term.pp lit_force Term.pp lit_forbid
    | CUF_forced2 {t;v1;v2;lit_v1;lit_v2} ->
      Fmt.fprintf out
        "(@[conflict-uf-forced2 `@[%a@]`@ (@[<- %a@ :by %a@])@ :or (@[<- %a@ :by %a@])@])"
        Term.pp t Value.pp v1 Term.pp lit_v1 Value.pp v2 Term.pp lit_v2
    | CUF_congruence {f;t1;t2} ->
      Fmt.fprintf out
        "(@[conflict-uf-congruence[%a]@ %a@ :and %a@])"
        Var.pp f Term.pp t1 Term.pp t2

  let pp_status out = function
    | Sat -> Fmt.string out "sat"
    | Unsat -> Fmt.string out "unsat"
    | Searching -> Fmt.string out "searching"
    | Conflict_bool c -> Fmt.fprintf out "(@[conflict %a@])" Clause.pp c
    | Conflict_uf cuf -> pp_conflict_uf out cuf

  let pp out (self:t) : unit =
    Fmt.fprintf out
      "(@[<hv>st @[<2>:status@ %a@]@ @[<2>:cs@ (@[<v>%a@])@]@ \
       @[<2>:trail@ %a@]@ @[<2>:env@ %a@]@])"
      pp_status self.status (pp_iter Clause.pp) (Clause.Set.to_seq self.cs)
      Trail.pp self.trail Env.pp self.env

  let parse_one (env:Env.t) (cs:Clause.t list) : (Env.t * Clause.t list) P.t =
    let open P in
    parsing "statement" @@ uncons string (function
        | "assert" ->
          (* assert *)
          parsing "assert" (list1 (Clause.parse env)) >|= fun c -> env, c::cs
        | "ty" ->
          (* new type *)
          parsing "type decl" (list1 string) >|= fun ty -> Env.add_ty (ID.make ty) env, cs
        | "fun" ->
          (* new function *)
          parsing "fun decl" (list2 string (Ty.parse env.Env.ty)) >|= fun (f,ty) ->
          let v = Var.make (ID.make f) ty in
          Env.add_var v env, cs
        | s -> failf "unknown statement %s" s)

  let rec parse_rec (env:Env.t) (cs:Clause.t list) : (Env.t * Clause.t list) P.t =
    let open P in
    is_nil >>= function
    | true -> return (env, List.rev cs)
    | false ->
      uncons (parse_one env cs) (fun (env, cs) -> parse_rec env cs)

  let parse : t P.t =
    let open P.Infix in
    parse_rec Env.empty [] >|= fun (env,cs) ->
    make env (Clause.Set.of_list cs) (Trail.empty ~env) Searching

  (* ######### *)

  let resolve_bool_conflict_ (self:t) : _ ATS.step option =
    let open ATS in
    match self.status with
    | Conflict_bool c when Clause.is_empty c ->
      Some (One (make self.env (Clause.Set.add c self.cs) self.trail Unsat, "learnt false"))
    | Conflict_bool c ->
      begin match self.trail with
        | Trail.Nil -> Some (Error "empty trail") (* should not happen *)
        | Trail.Cons {kind=BCP d;op=Trail.Assign {t=lit;value=Value.Bool false}; next;_} ->
          (* resolution *)
          assert (Clause.contains (Term.not_ lit) d);
          let res = Clause.union (Clause.remove (Term.not_ lit) d) (Clause.remove lit c) in
          let expl = Fmt.sprintf "resolve on `@[¬%a@]`@ with %a" Term.pp lit Clause.pp d in
          Some (One (make self.env self.cs next (Conflict_bool res), expl))
        | Trail.Cons {kind=BCP d;op=Assign{t=lit;_};next;_} when Clause.contains (Term.not_ lit) c ->
          (* resolution *)
          assert (Clause.contains lit d);
          let res = Clause.union (Clause.remove lit d) (Clause.remove (Term.not_ lit) c) in
          let expl = Fmt.sprintf "resolve on `@[%a@]`@ with %a" Term.pp lit Clause.pp d in
          Some (One (make self.env self.cs next (Conflict_bool res), expl))
        | Trail.Cons {kind=BCP _; op; next; _} ->
          let expl = Fmt.sprintf "consume-bcp %a" Term.pp (Op.lhs op) in
          Some (One (make self.env self.cs next self.status, expl))
        | Trail.Cons {kind=Eval; op; next; _} ->
          let expl = Fmt.sprintf "consume-eval %a" Term.pp (Op.lhs op) in
          Some (One (make self.env self.cs next self.status, expl))
        | Trail.Cons {kind=Decision; op=Op.Rewrite _; _ } -> assert false
        | Trail.Cons {kind=Decision; next; op=Op.Assign {t=lit;_}; _ } ->
          (* decision *)
          let c_reduced = Clause.filter_false (Trail.assign next) c in
          if Clause.is_empty c_reduced then (
            let expl = Fmt.sprintf "T-consume %a" Term.pp lit in
            Some (One (make self.env self.cs next (Conflict_bool c), expl))
          ) else if Clause.length c_reduced=1 then (
            (* normal backjump *)
            let expl = Fmt.sprintf "backjump with learnt clause %a" Clause.pp c in
            Some (One (make self.env (Clause.Set.add c self.cs) next Searching, expl))
          ) else if Clause.length c_reduced=2 then (
            (* semantic case split? *)
            let decision = Clause.choose c_reduced in
            let expl =
              Fmt.sprintf "backjump+semantic split with learnt clause %a@ @[<2>decide %a@ in %a@]"
                Clause.pp c Term.pp decision Clause.pp c_reduced
            in
            let trail = Trail.cons_assign ~env:self.env Trail.Decision decision Value.true_ next in
            Some (One (make self.env (Clause.Set.add c self.cs) trail Searching, expl))
          ) else (
            Some
              (Error
                 (Fmt.sprintf "backjump with clause %a@ but filter-false %a@ \
                               should have at most 2 lits"
                    Clause.pp c Clause.pp
                     c_reduced))
          )
      end
    | _ -> None

  let find_unit_c (self:t) : (Clause.t * Term.t) option =
    let assign = Trail.assign self.trail in
    Clause.Set.to_seq self.cs
    |> Iter.find_map
      (fun c ->
         (* non-false lits *)
         let c' = Clause.filter_false assign c in
         match Clause.as_unit c' with
         | Some l when not (Assignment.does_evaluate assign l) -> Some (c,l)
         | _ -> None)

  let propagate self : _ ATS.step option =
    match find_unit_c self with
    | Some (c,lit) ->
      let expl = Fmt.sprintf "@[<2>propagate %a@ from %a@]" Term.pp lit Clause.pp c in
      let trail = Trail.cons_assign ~env:self.env (BCP c) lit Value.true_ self.trail in
      Some (ATS.One (make self.env self.cs trail Searching, expl))
    | None -> None

  (* find [a=b] where [a] and [b] are assigned *)
  let propagate_uf_eq self : (_*_) ATS.step option =
    let ass = Trail.assign self.trail in
    let has_ass t = Assignment.does_evaluate ass t in
    all_vars self
    |> Term.Set.to_seq
    |> Iter.filter (fun t -> not @@ has_ass t)
    |> Iter.find_map
      (fun t ->
        match Term.view t with
          | Term.Eq (a,b) when has_ass a && has_ass b ->
            let value =
              Value.bool
                (Value.equal
                   (Assignment.evaluate_exn ass a)
                   (Assignment.evaluate_exn ass b))
            in
            let trail = Trail.cons_assign ~env:self.env Trail.Eval t value self.trail in
            let expl = Fmt.asprintf "eval %a" Term.pp t in
            Some (ATS.One (make self.env self.cs trail Searching, expl))
          | _ -> None)

  let is_searching self = match self.status with
    | Searching -> true
    | _ -> false

  let decide self : _ ATS.step option =
    (* try to decide *)
    let vars = to_decide self in
    if Term.Set.is_empty vars then (
      (* full model, we're done! *)
      Some (ATS.One (make self.env self.cs self.trail Sat, "all vars decided"))
    ) else (
      (* multiple possible decisions *)
      let decs =
        Term.Set.to_seq vars
        |> Iter.flat_map_l
          (fun x ->
             let mk_ v value =
               make self.env self.cs
                 (Trail.cons_assign ~env:self.env Decision v value self.trail)
                 Searching,
               Fmt.sprintf "decide %a <- %a" Term.pp v Value.pp value
             in
             if Term.is_bool x then (
               [mk_ x Value.true_; mk_ x Value.false_]
             ) else (
               let domain = uf_domain self in
               match Term.Map.get x domain with
               | None -> [mk_ x @@ Value.unin (Term.ty x) 0]
               | Some (UFD_conflict_forbid _ | UFD_conflict_forced2 _) ->
                 assert false
               | Some (UFD_forced (v,_)) -> [mk_ x v]
               | Some (UFD_forbid l) ->
                 let value =
                   Iter.(0--max_int)
                   |> Iter.find_map (fun i ->
                       let value = Value.unin (Term.ty x) i in
                       if List.for_all (fun (v',_) -> not (Value.equal value v')) l
                       then Some value else None)
                   |> CCOpt.get_exn
                 in
                 [mk_ x value]

             ))
        |> Iter.to_rev_list
      in
      Some (ATS.Choice decs)
    )

  let find_false_clause (self:t) : _ option =
    let ass = Trail.assign self.trail in
    match Iter.find_pred (Clause.eval_to_false ass) (Clause.Set.to_seq self.cs) with
    | None -> None
    | Some c ->
      (* conflict! *)
      Some (ATS.One (make self.env self.cs self.trail (Conflict_bool c), "false clause"))

  let find_uf_domain_conflict (self:t) : _ option =
    let domain = uf_domain self in
    let l =
      Term.Map.to_seq domain
      |> Iter.filter_map
          (fun (t,dom) ->
            match dom with
            | UFD_conflict_forbid (v,t1,t2) ->
              Some (t, Conflict_uf (CUF_forbid {t;v;lit_force=t1; lit_forbid=t2}))
            | UFD_conflict_forced2 (v1,t1,v2,t2) ->
              Some (t, Conflict_uf (CUF_forced2 {t;v1;lit_v1=t1;v2;lit_v2=t2}))
            | _ -> None)
      |> Iter.to_rev_list
    in
    let mk_expl t = Fmt.asprintf "UF domain conflict on %a" Term.pp t in
    begin match l with
      | [] -> None
      | [t, c] ->
        Some (ATS.One (make self.env self.cs self.trail c, mk_expl t))
      | cs ->
        let choices =
          List.map
            (fun (t,c) -> make self.env self.cs self.trail c, mk_expl t) cs
        in
        Some (ATS.Choice choices)
    end

  let find_congruence_conflict (self:t) : _ option =
    let ass = Trail.assign self.trail in
    let sigs = uf_sigs self in
    let has_ass x = Assignment.does_evaluate ass x in
    let get_ass x = Assignment.evaluate_exn ass x in
    let l =
      Trail.iter_op self.trail
      |> Iter.filter_map
        (function
          | Op.Rewrite {l=t;r} ->
            begin match Term.view t, Assignment.evaluate ass r with
              | Term.App (f, l), Some v when List.for_all has_ass l ->
                (* see if the signature is compatible with [v] *)
                begin match SigMap.get (f, List.map get_ass l) sigs with
                  | None -> assert false
                  | Some (v2,_) when Value.equal v v2 -> None (* compatible *)
                  | Some (_v2,t2) ->
                    let cuf = CUF_congruence {f; t1=t;t2} in
                    Some (t, Conflict_uf cuf)
                end
              | _ -> None
            end
          | Op.Assign {t;value=v} ->
            begin match Term.view t with
              | Term.App (f, l) when List.for_all has_ass l ->
                (* see if the signature is compatible with [v] *)
                begin match SigMap.get (f, List.map get_ass l) sigs with
                  | None -> assert false
                  | Some (v2,_) when Value.equal v v2 -> None (* compatible *)
                  | Some (_v2,t2) ->
                    let cuf = CUF_congruence {f; t1=t;t2} in
                    Some (t, Conflict_uf cuf)
                end
              | _ -> None
            end)
      |> Iter.to_rev_list
    in
    let mk_expl t = Fmt.asprintf "UF congruence conflict on %a" Term.pp t in
    begin match l with
      | [] -> None
      | [t, c] ->
        Some (ATS.One (make self.env self.cs self.trail c, mk_expl t))
      | cs ->
        let choices =
          List.map
            (fun (t,c) -> make self.env self.cs self.trail c, mk_expl t) cs
        in
        Some (ATS.Choice choices)
    end

  (* assuming [eq] is an equation [t=u] or [u=t], return [u] *)
  let get_eq_other_side (t:Term.t) ~(eq:Term.t) : Term.t =
    match Term.view eq with
    | Term.Eq (a,b) when Term.equal a t -> b
    | Term.Eq (a,b) when Term.equal b t -> a
    | _ -> Util.errorf "get_eq_other_side of %a in %a" Term.pp t Term.pp eq

  let mk_uf_lemma (self:t) (cuf:conflict_uf) : Clause.t =
    let ass = Trail.assign self.trail in
    match cuf with
    | CUF_forbid { t; v=_; lit_force; lit_forbid } ->
      (* learn transitivity lemma *)
      let t1 = get_eq_other_side t ~eq:lit_forbid in
      let t2 = get_eq_other_side t ~eq:lit_force in
      Clause.of_list [Term.eq t1 t; Term.neq t2 t; Term.neq t1 t2]
    | CUF_forced2 { t; v1=_; v2=_; lit_v1; lit_v2 } ->
      (* transitivity lemma *)
      let t1 = get_eq_other_side t ~eq:lit_v1 in
      let t2 = get_eq_other_side t ~eq:lit_v2 in
      Clause.of_list [Term.neq t1 t; Term.neq t2 t; Term.eq t1 t2]
    | CUF_congruence { f; t1; t2; } ->
      (* congruence lemma *)
        begin match Term.view t1, Term.view t2 with
        | Term.App (f1,l1), Term.App (f2, l2) ->
          assert (Var.equal f f1 && Var.equal f f2 && List.length l1 = List.length l2);
          let hyps = CCList.map2 Term.neq l1 l2 in
          let concl =
            (* one of the two terms is false in current trail *)
            if Term.is_bool t1 then (
              match Clause.eval_lit ass t1, Clause.eval_lit ass t2 with
              | Some true, Some false ->
                [Term.not_ t1; t2]
              | Some false, Some true ->
                [Term.not_ t2; t1]
              | v1, v2 ->
                Util.errorf "cannot find boolean congruence lemma@ for %a[%a] and %a[%a]"
                  Term.pp t1 (Fmt.opt Fmt.bool) v1 Term.pp t2 (Fmt.opt Fmt.bool) v2
            ) else (
              [Term.eq t1 t2]
            )
          in
          Clause.of_list (concl @ hyps)
        | _ -> assert false
        end

  (* learn some UF lemma and then do resolution on it *)
  let solve_uf_domain_conflict (self:t) : _ option =
    match self.status with
    | Searching | Sat | Unsat | Conflict_bool _ -> None
    | Conflict_uf cuf ->
      (* learn a UF lemma *)
      let lemma = mk_uf_lemma self cuf in
      let expl = Fmt.asprintf "add UF lemma %a" Clause.pp lemma in
      (* lemma must be false *)
      let reduced = Clause.filter_false (Trail.assign self.trail) lemma in
      if not @@ Clause.is_empty reduced then (
        Util.errorf "bad lemma: %a@ reduced: %a" Clause.pp lemma Clause.pp reduced;
      );
      Some (ATS.One (make self.env self.cs self.trail (Conflict_bool lemma), expl))

  let if_searching f self = match self.status with
    | Searching -> f self
    | _ -> None

  let is_done (self:t) =
    match self.status with
    | Sat | Unsat -> Some ATS.Done
    | _ -> None

  let rules : _ ATS.rule list list = [
    [is_done];
    [resolve_bool_conflict_; solve_uf_domain_conflict;];
    [if_searching find_false_clause;
     if_searching find_uf_domain_conflict;
     if_searching find_congruence_conflict;
    ];
    [if_searching propagate];
    [if_searching propagate_uf_eq];
    [if_searching decide];
  ]
end

module A = struct
  let name = "mcsup"
  module State = State
  let rules = State.rules
end

let ats : ATS.t = (module ATS.Make(A))
