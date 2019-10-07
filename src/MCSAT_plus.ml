open Util

include Smt_types_1

module SigMap = CCMap.Make(struct
    type t = Var.t * Value.t list
    let compare (f1,l1) (f2,l2) =
      if Var.equal f1 f2 then CCList.compare Value.compare l1 l2
      else Var.compare f1 f2
  end)

module Op : sig
  type t =
    | Assign of {t: Term.t; value: Value.t; } 

  val lhs : t -> Term.t
  val pp : t Fmt.printer
end = struct
  type t =
    | Assign of {t: Term.t; value: Value.t; } 

  let[@inline] lhs = function
    | Assign {t;_} -> t

  let pp out = function
    | Assign {t; value} -> Fmt.fprintf out "(@[<2>%a@ <- %a@])" Term.pp t Value.pp value
end

module Assignment : sig
  type t

  type op = Op.t =
    | Assign of {t: Term.t; value: Value.t; } 

  val eval : t -> Term.t -> Value.t option
  val eval_exn : t -> Term.t -> Value.t
  val can_eval : t -> Term.t -> bool

  val empty : t
  val add_assign : Term.t -> Value.t -> t -> t
  val add_op : op -> t -> t

  val to_iter : t -> op Iter.t
  val length : t -> int

  val pp : t Fmt.printer
end = struct
  module TM = Term.Map
  type t = {
    assign: Value.t TM.t;
  }

  let empty : t = { assign=TM.empty; }

  type op = Op.t =
    | Assign of {t: Term.t; value: Value.t; } 

  let to_iter self =
    TM.to_seq self.assign |> Iter.map (fun (t,value) -> Assign {t;value})

  let pp out self =
    Fmt.fprintf out "(@[<hv>%a@])" (Util.pp_iter Op.pp) (to_iter self)

  let add_assign t value self : t =
    let assign =
      if Value.is_bool value then (
        self.assign |> Term.Map.add t value
        |> Term.Map.add (Term.not_ t) (Value.not_ value)
      ) else (
        self.assign |> Term.Map.add t value
      )
    in
    {assign}

  let add_op op self : t = match op with
    | Assign {t; value} -> add_assign t value self

  let length self = TM.cardinal self.assign

  let eval (self:t) (t:Term.t) : _ option =
    (* Fmt.printf "evaluate %a in %a@." Term.pp t pp self; *)
    TM.get t self.assign

  let can_eval self t = TM.mem t self.assign
  let eval_exn self t = match eval self t with
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
  let mem = Term.Set.mem
  let remove l c : t = Term.Set.remove l c
  let union = Term.Set.union
  let add t c =
    if Term.is_false t then c else Term.Set.add t c
  let add_l l c = List.fold_right add l c
  let lits c = Term.Set.to_seq c
  let for_all = Term.Set.for_all
  let filter = Term.Set.filter
  let of_list = Term.Set.of_list
  let map f set =
    Term.Set.fold (fun x res -> Term.Set.add (f x) res) set Term.Set.empty
  let replace ~old ~by c = map (Term.replace ~old ~by) c

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
      begin match Assignment.eval ass a, Assignment.eval ass b with
        | Some va, Some vb -> Some (Value.equal va vb)
        | _ -> None
      end
    | Term.Not u ->
      CCOpt.map not (eval_lit_semantic ass u)
    | _ -> None

  (* semantic + trail evaluation *)
  let eval_lit (ass:Assignment.t) (t:Term.t) : bool option =
    match Assignment.eval ass t with
    | Some (Value.Bool b) -> Some b
    | Some _ -> assert false
    | None -> eval_lit_semantic ass t

  (* can [t] eval to false? *)
  let lit_eval_to_false (ass:Assignment.t) (t:Term.t) : bool =
    match Assignment.eval ass t, eval_lit_semantic ass t with
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

module Trail : sig
  type kind =
    | Decision
    | BCP of Clause.t
    | Eval of Term.t list (* responsible for evaluation *)
    | Assign_propagate of {
        (* assigning [t] to the same value as [from] bc [guard => t=from] *)
        guard: Term.t list;
        from: Term.t;
      }
  type op = Assignment.op
  type t

  val pp : t Fmt.printer
  val pp_trail_elt : (kind * int * op) Fmt.printer
  val pp_kind : kind Fmt.printer

  val env : t -> Env.t
  val pop : t -> (kind * op * t) option
  val assign : t -> Assignment.t
  val assigned_vars : t -> Var.t list
  val length : t -> int
  val n_decisions : t -> int
  val map : (Term.t -> Term.t) -> t -> t

  val empty : Env.t -> t
  val level : t -> int
  val cons : kind -> op -> t -> t
  val cons_assign : kind -> Term.t -> Value.t -> t -> t
  val to_iter : t -> (kind * int * op) Iter.t
  val iter_terms : t -> Term.t Iter.t
  val iter_ops : t -> Op.t Iter.t
end = struct
  type kind =
    | Decision
    | BCP of Clause.t
    | Eval of Term.t list (* responsible for evaluation *)
    | Assign_propagate of {
        (* assigning [t] to the same value as [from] bc [guard => t=from] *)
        guard: Term.t list;
        from: Term.t;
      }
  type op = Assignment.op =
    | Assign of { t: Term.t; value: Value.t; }
  type t = {
    env: Env.t;
    stack: stack;
    _assign: Assignment.t lazy_t; (* assignment from this trail *)
    _assigned_vars: Var.t list; (* subset of unit variables assigned so far, top to bottom *)
  }
  and stack =
    | Nil
    | Cons of {
        kind: kind;
        op: op;
        next: t;
        level: int;
      }


  let env self = self.env
  let pop self = match self.stack with
    | Nil -> None
    | Cons {kind; op; next; _} -> Some (kind, op, next)

  let[@inline] assign self = Lazy.force self._assign
  let[@inline] assigned_vars self = self._assigned_vars
  let[@inline] level self = match self.stack with
    | Nil -> 0
    | Cons {level=l;_} -> l

  let cons kind (op:op) (next:t) : t =
    (* Format.printf "trail.cons %a <- %a@." Term.pp lit Value.pp value; *)
    let env = next.env in
    let level = match kind with
      | Decision -> 1 + level next
      | BCP _ | Assign_propagate _ | Eval _ -> level next
    and _assign = lazy (
      let a = assign next in
      Assignment.add_op op a
    )
    and _assigned_vars =
      let l = assigned_vars next in
      match op with
      | Op.Assign {t;_} ->
        match Term.view t with
          | App (f, []) -> f :: l
          | _ -> l
    in
    {env; _assign; _assigned_vars; stack=Cons { kind; op; next; level; }}

  let cons_assign kind (t:Term.t) (value:Value.t) next : t =
    let t, value =
      if Term.sign t then t, value else Term.not_ t, Value.not_ value in
    cons kind (Assign {t; value}) next

  let unit_true = Clause.of_list [Term.true_] (* axiom: [true] *)
  let empty env =
    let e = {
      env; stack=Nil; _assigned_vars=[];
      _assign=lazy Assignment.empty;
    } in
    cons_assign (BCP unit_true) Term.true_ Value.true_  e

  let rec map f self = {self with stack=map_stack f self.stack}
  and map_stack f self = match self with
    | Nil -> Nil
    | Cons r ->
      let op = match r.op with
        | Op.Assign {t;value} -> Op.Assign {t=f t; value}
      in
      Cons {r with next=map f r.next; op; }

  let rec iter k self = match self.stack with
    | Nil -> ()
    | Cons {kind;op;next;level;_} ->
      k (kind, level, op);
      iter k next

  let to_iter (tr:t) : (kind * int * op) Iter.t = fun k -> iter k tr
  let iter_terms (tr:t) : Term.t Iter.t =
    to_iter tr |> Iter.map (fun (_,_,op) -> Op.lhs op)
  let iter_ops (tr:t) : op Iter.t = to_iter tr |> Iter.map (fun (_,_,op) -> op)
  let length tr = to_iter tr |> Iter.length
  let n_decisions tr = to_iter tr |> Iter.filter (fun (k,_,_) -> k=Decision) |> Iter.length

  let pp_trail_elt out (k,level,op) =
    let cause = match k with
      | Decision -> "*" | BCP _ -> ""
      | Eval _ -> "$" | Assign_propagate _ -> "<-=" in
    Fmt.fprintf out "@[<h>[%d%s]%a@]" level cause Op.pp op

  let pp_kind out = function
    | Decision -> Fmt.string out "decision"
    | Eval l -> Fmt.fprintf out "(@[eval@ %a@])" (Util.pp_list Term.pp) l
    | BCP c -> Fmt.fprintf out "(@[bcp@ :clause %a@])" Clause.pp c
    | Assign_propagate {guard; from} ->
      Fmt.fprintf out "(@[assign-propagate@ :eq-to %a@ :guard %a@])"
        Term.pp from (Fmt.Dump.list Term.pp) guard

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

  type subst = Term.t Term.Map.t

  type uf_domain =
    | UFD_forced of Value.t * Term.t
    | UFD_forbid of (Value.t * Term.t) list
    | UFD_conflict_forbid of Value.t * Term.t * Term.t
    | UFD_conflict_forced2 of Value.t * Term.t  * Value.t * Term.t 

  type t = {
    env: Env.t;
    cs: Clause.Set.t;
    trail: Trail.t;
    subst: subst; (* global substitution*)
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
    let is_ass x = Assignment.can_eval ass x in
    (* pairs of impossible assignments *)
    let pairs : (Term.t * Term.t * _) list =
      Trail.iter_ops trail
      |> Iter.filter_map
        (function
          | Op.Assign {t; value} ->
            begin match Term.view t, value with
              | Term.Eq (a,b), Value.Bool bool when is_ass a && not (is_ass b) ->
                let value = Assignment.eval_exn ass a in
                Some (t, b, if bool then `Forced value else `Forbid value)
              | Term.Eq (a,b), Value.Bool bool when is_ass b && not (is_ass a) ->
                let value = Assignment.eval_exn ass b in
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
    let is_ass x = Assignment.can_eval ass x in
    Trail.iter_ops trail
    |> Iter.filter_map
      (function
        | Op.Assign {t; value=v} ->
          begin match Term.view t with
            | Term.App (f, l) when List.for_all is_ass l ->
              Some ((f, List.map (Assignment.eval_exn ass) l), (v,t))
            | _ -> None
          end)
    |> SigMap.of_seq

  (* main constructor *)
  let make (env:Env.t) (cs:Clause.Set.t) (trail:Trail.t) (subst:subst) status : t =
    let _all_vars = lazy (
      Iter.(
        Clause.Set.to_seq cs
        |> flat_map Clause.lits |> flat_map Term.sub_all |> map Term.abs)
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
    { env; cs; trail; status; subst; _all_vars; _to_decide; _uf_sigs; _uf_domain; }

  let empty : t =
    make Env.empty Clause.Set.empty (Trail.empty Env.empty) Term.Map.empty Searching

  let update ?cs ?env ?trail ?subst ?status (self:t) : t =
    let get_or x y = CCOpt.get_or ~default:x y in
    let cs = get_or self.cs cs in
    let env = get_or self.env env in
    let trail = get_or self.trail trail in
    let subst = get_or self.subst subst in
    let status = get_or self.status status in
    make env cs trail subst status

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
      "(@[<hv>st @[<2>:status@ %a@]@ @[<2>:cs[%d]@ (@[<v>%a@])@]@ \
       @[<2>:trail@ %a@]@ @[<2>:env@ %a@]@])"
      pp_status self.status (Clause.Set.cardinal self.cs)
      (pp_iter Clause.pp) (Clause.Set.to_seq self.cs)
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
    make env (Clause.Set.of_list cs) (Trail.empty env) Term.Map.empty Searching

  (* ######### *)

  (* does [lit] reduce to [false] (partly) because of [l]?
     and in that case, rewrite [l] into [r] in it. *)
  let rw_in_lit_if_evals_to_false_ (ass:Assignment.t) ~l ~r (lit:Term.t) : _ option =
    let rec rw_rec t =
      match Term.view t with
      | _ when Term.equal t l -> Some r
      | Term.Bool _ -> None
      | Term.Not u -> CCOpt.map Term.not_ (rw_rec u)
      | Term.If _ -> None (* TODO: should have been eliminated *)
      | Term.Eq (a, b) ->
        begin match Term.equal a l, Term.equal b l with
          | true, true -> Some (Term.eq r r) (* ?! *)
          | true, false -> Some (Term.eq r b)
          | false, true -> Some (Term.eq a r)
          | false, false -> None
        end
      | Term.App (f, args) ->
        let did_replace = ref false in
        let args' =
          List.map
            (fun t ->
               if Term.equal t l then (did_replace := true; r) else t)
            args in
        if !did_replace then Some (Term.app f args') else None
    in
    match Clause.eval_lit_semantic ass lit with
    | Some false -> rw_rec lit
    | _ -> None

  let rw_in_clause_if_evals_to_false (ass:Assignment.t) ~l ~r (c:Clause.t) : Clause.t option =
    let matched = ref false in
    let c' =
      Clause.map
        (fun lit ->
           match rw_in_lit_if_evals_to_false_ ass ~l ~r lit with
           | None -> lit
           | Some lit' -> matched := true; lit')
        c
    in
    if !matched then Some c' else None

  (* turn [t[if a b c]] into [t[u] & a=>u=b & ¬a => u=c] *)
  let remove_ifs (self:t) : _ ATS.step option =
    let vars = all_vars self in
    let as_if t = match Term.view t with
      | If (a,b,c) -> Some (t,(a,b,c))
      | _ -> None
    in
    match Term.Set.to_seq vars |> Iter.find_map as_if with
    | None -> None
    | Some (t,(a,b,c)) ->
      let id = ID.makef "_if_%d" (Term.Map.cardinal self.subst) in
      let u = Term.const @@ Var.make id (Term.ty t) in
      let subst = Term.Map.add t u self.subst in
      let trail = Trail.map (Term.replace ~old:t ~by:u) self.trail in
      let c1 = Clause.of_list [Term.not_ a; Term.eq u b] in
      let c2 = Clause.of_list [a; Term.eq u c] in
      let cs =
        Clause.Set.add c1 @@
        Clause.Set.add c2 @@
        Clause.Set.map (Clause.replace ~old:t ~by:u) self.cs
      in
      let expl = Fmt.sprintf "lift-ite %a@ into %a" Term.pp t Term.pp u in
      let st' = lazy (make self.env cs trail subst Searching) in
      Some (ATS.One (st', false, expl))

  let resolve_bool_conflict_ (self:t) : _ ATS.step option =
    let open ATS in
    match self.status with
    | Conflict_bool c when Clause.is_empty c ->
      Some (One (lazy (update self ~cs:(Clause.Set.add c self.cs) ~status:Unsat), false, "learnt false"))
    | Conflict_bool c when Clause.mem Term.false_ c ->
      let c = Clause.remove Term.false_ c in
      Some (One (lazy (update self ~status:(Conflict_bool c)), false, "remove false"))
    | Conflict_bool c ->
      let ass = Trail.assign self.trail in
      begin match Trail.pop self.trail with
        | None -> Some (Error "empty trail") (* should not happen *)
        | Some (BCP d, Op.Assign {t=lit;value=Value.Bool false}, next) ->
          (* resolution *)
          assert (Clause.contains (Term.not_ lit) d);
          let res = Clause.union (Clause.remove (Term.not_ lit) d) (Clause.remove lit c) in
          let expl = Fmt.sprintf "resolve on `@[¬%a@]`@ with %a" Term.pp lit Clause.pp d in
          Some (One (lazy (update self ~trail:next ~status:(Conflict_bool res)), false, expl))
        | Some (BCP d, Op.Assign{t=lit;_}, next) when Clause.contains (Term.not_ lit) c ->
          (* resolution *)
          assert (Clause.contains lit d);
          let res = Clause.union (Clause.remove lit d) (Clause.remove (Term.not_ lit) c) in
          let expl = Fmt.sprintf "resolve on `@[%a@]`@ with %a" Term.pp lit Clause.pp d in
          Some (One (lazy (update self ~trail:next ~status:(Conflict_bool res)), false, expl))
        | Some (BCP _, op, next) ->
          let expl = Fmt.sprintf "consume-bcp %a" Term.pp (Op.lhs op) in
          Some (One (lazy (update self ~trail:next ~status:self.status), false, expl))
        | Some (Eval _, (Op.Assign _ as op), next) ->
          let expl = Fmt.sprintf "consume-eval %a" Term.pp (Op.lhs op) in
          Some (One (lazy (update self ~trail:next ~status:self.status), false, expl))
        | Some (Assign_propagate {guard; from}, Op.Assign {t; value=_}, next) ->
          (* find lits of [c] evaluating to [false] because of [t],
             replace with [from] and add [¬guard] as guard,
             otherwise just consume.
             This rule corresponds to Dejan'17's semantic propagation. *)
          Format.printf "@[<2>try to rw %a@ into %a@ in %a@ via assign-propagate %a@]@."
            Term.pp t Term.pp from Clause.pp c (Fmt.Dump.list Term.pp) guard;
          begin match rw_in_clause_if_evals_to_false ass ~l:t ~r:from c with
            | Some c' ->
              let c' = Clause.add_l (List.map Term.not_ guard) c' in
              let expl = Fmt.sprintf "paramod-assign @[%a --> %a@]@ :guard %a@ :into %a"
                  Term.pp t Term.pp from (Fmt.Dump.list Term.pp) guard Clause.pp c' in
              Some (One (lazy (update self ~trail:next ~status:(Conflict_bool c')), false, expl))
            | None ->
              let expl =
                Fmt.sprintf "consume-assign-prop %a@ :guard %a"
                  Term.pp t (Fmt.Dump.list Term.pp) guard in
              Some (One (lazy (update self ~trail:next), false, expl))
          end
        | Some (Decision, Op.Assign {t;_}, next) ->
          (* decision *)
          let c_reduced = Clause.filter_false (Trail.assign next) c in
          if Clause.is_empty c_reduced then (
            let expl = Fmt.sprintf "T-consume %a" Term.pp t in
            Some (One (lazy (update self ~trail:next ~status:(Conflict_bool c)), false, expl))
          ) else if Clause.length c_reduced=1 then (
            (* normal backjump *)
            let expl = Fmt.sprintf "backjump with learnt clause %a" Clause.pp c in
            let st' = lazy (
              update self ~cs:(Clause.Set.add c self.cs) ~trail:next ~status:Searching
            ) in
            Some (One (st', false, expl))
          ) else (
            (* semantic case split *)
            assert (not (Term.is_bool t));
            let decision = Clause.choose c_reduced in
            let expl =
              Fmt.sprintf "backjump+semantic split with learnt clause %a@ @[<2>decide %a@ in %a@]"
                Clause.pp c Term.pp decision Clause.pp c_reduced
            in
            let trail = Trail.cons_assign Trail.Decision decision Value.true_ next in
            let st' = lazy (
              update self ~cs:(Clause.Set.add c self.cs) ~trail ~status:Searching
            ) in
            Some (One (st', true, expl))
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
         | Some l when not (Assignment.can_eval assign l) -> Some (c,l)
         | _ -> None)

  let propagate self : _ ATS.step option =
    match find_unit_c self with
    | Some (c,lit) ->
      let expl = Fmt.sprintf "@[<2>propagate %a@ from %a@]" Term.pp lit Clause.pp c in
      let trail = Trail.cons_assign (BCP c) lit Value.true_ self.trail in
      Some (ATS.One (lazy (update self ~trail ~status:Searching), false, expl))
    | None -> None

  (* find [a=b] where [a] and [b] are assigned *)
  let propagate_uf_eq self : _ ATS.step option =
    let ass = Trail.assign self.trail in
    let has_ass t = Assignment.can_eval ass t in
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
                   (Assignment.eval_exn ass a)
                   (Assignment.eval_exn ass b))
            in
            let trail = Trail.cons_assign (Trail.Eval [a;b]) t value self.trail in
            let expl = Fmt.asprintf "eval %a" Term.pp t in
            Some (ATS.One (lazy (update self ~trail ~status:Searching), false, expl))
          | _ -> None)

  (* find [a = b] where [b <- v] and [a] not assigned, and add [a <- v] *)
  let eq_assign_propagate self : _ ATS.step option =
    let ass = Trail.assign self.trail in
    let has_ass t = Assignment.can_eval ass t in
    let get_ass t = Assignment.eval_exn ass t in
    let ops =
      Trail.iter_ops self.trail
      |> Iter.filter_map
        (function
          | Op.Assign {t; value=Value.Bool true} ->
            begin match Term.view t with
              | Term.Eq (a,b) when not (has_ass a) && has_ass b ->
                let v = get_ass b in
                let expl =
                  Fmt.asprintf "assign %a to %a by =<- %a"
                    Term.pp a Value.pp v Term.pp b
                and kind = Trail.Assign_propagate {from=b; guard=[t]} in
                Some ((kind, a, v), expl)
              | Term.Eq (a,b) when has_ass a && not (has_ass b) ->
                let v = get_ass a in
                let expl =
                  Fmt.asprintf "assign %a to %a by =<- %a"
                    Term.pp b Value.pp v Term.pp a
                and kind = Trail.Assign_propagate {from=a; guard=[t]} in
                Some ((kind, b, v), expl)
              | _ -> None
            end
          | _ -> None)
      |> Iter.to_rev_list
    in
    match ops with
    | [] -> None
    | l ->
      let ops, expl = List.split l in
      let expl = String.concat "\n" expl in
      let trail =
        List.fold_left (fun tr (k,t,v) -> Trail.cons_assign k t v tr) self.trail ops
      in
      Some (ATS.One (lazy (update self ~trail ~status:Searching), false, expl))

  (* find [f(t1…tn)] where [ti <- vi] and there is an entry [f(v1…vn) -> v]
     in the congruence table, and add [f(t1…tn) <- v] *)
  let eq_assign_congruence self : _ option =
    let ass = Trail.assign self.trail in
    let has_ass t = Assignment.can_eval ass t in
    let get_ass t = Assignment.eval_exn ass t in
    let ops =
      to_decide self
      |> Term.Set.to_seq
      |> Iter.filter_map
        (fun t ->
           assert (not (has_ass t));
           match Term.view t with
           | Term.App (f, (_::_ as args)) when List.for_all has_ass args ->
             let ctbl = uf_sigs self in
             begin match SigMap.get (f, List.map get_ass args) ctbl with
               | None -> None
               | Some (v, u) ->
                 let expl =
                   Fmt.asprintf "assign %a to %a by congruence with %a"
                     Term.pp t Value.pp v Term.pp u
                 and kind =
                   let args_u = match Term.view u with
                     | Term.App (f', l') ->
                       assert (Var.equal f f' && List.length args = List.length l');
                       l'
                     | _ -> assert false
                   in
                   Trail.Assign_propagate
                     {from=u; guard=List.map2 Term.eq args args_u}
                 in
                 Some ((kind, t, v), expl)
             end
           | _ -> None)
      |> Iter.to_rev_list
    in
    match ops with
    | [] -> None
    | l ->
      let ops, expl = List.split l in
      let expl = String.concat "\n" expl in
      let trail =
        List.fold_left (fun tr (k,t,v) -> Trail.cons_assign k t v tr) self.trail ops
      in
      Some (ATS.One (lazy (update self ~trail ~status:Searching), false, expl))

  let decide self : _ ATS.step option =
    (* try to decide *)
    let vars = to_decide self in
    if Term.Set.is_empty vars then (
      (* full model, we're done! *)
      Some (ATS.One (lazy (update self ~status:Sat), false, "all vars decided"))
    ) else (
      (* multiple possible decisions *)
      let decs =
        Term.Set.to_seq vars
        |> Iter.flat_map_l
          (fun x ->
             let mk_ v value =
               let w = if Term.is_bool x then 1 else Term.weight x in
               let st' = lazy (
                 update self
                   ~trail:(Trail.cons_assign Decision v value self.trail)
                   ~status:Searching)
               in
               w, (st', true, Fmt.sprintf "decide %a <- %a" Term.pp v Value.pp value)
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
        |> List.sort (fun (w1,_)(w2,_) -> CCInt.compare w1 w2)
        |> CCList.map snd
      in
      Some (ATS.Choice decs)
    )

  let find_false_clause (self:t) : _ option =
    let ass = Trail.assign self.trail in
    match Iter.find_pred (Clause.eval_to_false ass) (Clause.Set.to_seq self.cs) with
    | None -> None
    | Some c ->
      (* conflict! *)
      Some (ATS.One (lazy (update self ~status:(Conflict_bool c)), false, "false clause"))

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
        Some (ATS.One (lazy (update self ~status:c), false, mk_expl t))
      | cs ->
        let choices =
          List.map
            (fun (t,c) -> lazy (update self ~status:c), false, mk_expl t) cs
        in
        Some (ATS.Choice choices)
    end

  let find_congruence_conflict (self:t) : _ option =
    let ass = Trail.assign self.trail in
    let sigs = uf_sigs self in
    let has_ass x = Assignment.can_eval ass x in
    let get_ass x = Assignment.eval_exn ass x in
    let l =
      Trail.iter_ops self.trail
      |> Iter.filter_map
        (function
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
        Some (ATS.One (lazy (update self ~status:c), false, mk_expl t))
      | cs ->
        let choices =
          List.map
            (fun (t,c) -> lazy (update self ~status:c), false, mk_expl t) cs
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
      Some (ATS.One (lazy (update self ~status:(Conflict_bool lemma)), false, expl))

  let if_searching f self = match self.status with
    | Searching -> f self
    | _ -> None

  let is_done (self:t) =
    match self.status with
    | Sat | Unsat -> Some ATS.Done
    | _ -> None

  let rules : _ ATS.rule list list = [
    [is_done];
    [if_searching remove_ifs;];
    [resolve_bool_conflict_; solve_uf_domain_conflict;];
    [if_searching find_false_clause;
    ];
    [if_searching propagate];
    [if_searching eq_assign_propagate; if_searching eq_assign_congruence];
    [
      if_searching find_uf_domain_conflict;
      if_searching find_congruence_conflict;
    ];
    [if_searching propagate_uf_eq];
    [if_searching decide];
    [fun _ -> Some (Error "no rule applies!")];
  ]
end

module A = struct
  let name = "mcsat+"
  module State = State
  let rules = State.rules
end

let ats : ATS.t = (module ATS.Make(A))
