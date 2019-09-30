(** {1 Types shared by SMT instances} *)
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
  type t = Bool of bool | Unin of Var.t

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

  val is_false : t -> bool
  val is_true : t -> bool

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

  let is_false t = match t.view with Bool false -> true | _ -> false
  let is_true t = match t.view with Bool true -> true | _ -> false

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

