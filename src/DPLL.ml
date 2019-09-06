open Util

module Lit = struct
  type t = int
  let compare = CCInt.compare
  let abs = abs
  let pp = Fmt.int
  let parse = P.(skip_white *> U.int)
  module As_key = struct type nonrec t = t let compare=compare end
  module Set = CCSet.Make(As_key)
  module Map = CCMap.Make(As_key)
end

module Clause = struct
  type t = Lit.t list
  let pp out c = Fmt.fprintf out "(@[%a@])" (pp_list Lit.pp) c

  let parse : t P.t =
    let open P in
    (skip_white *> char '(' *> many (try_ Lit.parse)) <* try_ (skip_white <* char ')')
end

module State = struct
  type trail_kind = Decision | Prop of Clause.t
  type trail_elt = trail_kind * Lit.t
  type trail = trail_elt list
  type status =
    | Sat
    | Unsat
    | Conflict of Clause.t
    | Idle
  type t = {
    cs: Clause.t list;
    trail: trail;
    status: status;
    _all_vars: Lit.Set.t lazy_t;
    _to_decide: Lit.Set.t lazy_t;
    _assign: bool Lit.Map.t lazy_t; (* assignment, from trail *)
  }

  (* main constructor *)
  let make cs trail status : t =
    let _all_vars = lazy (
      Iter.(of_list cs |> flat_map of_list |> map Lit.abs) |> Lit.Set.of_seq;
    ) in
    let _to_decide = lazy (
      let lazy all = _all_vars in
      let in_trail =
        Iter.(of_list trail |> map snd |> map Lit.abs) |> Lit.Set.of_seq in
      Lit.Set.diff all in_trail
    ) in
    let _assign = lazy (
      Iter.(of_list trail
            |> map snd |> flat_map_l (fun i -> [i, true; -i, false]))
      |> Lit.Map.of_seq
    ) in
    {cs;trail;status;_all_vars; _to_decide; _assign}

  let empty : t = make [] [] Idle

  let pp_status out = function
    | Sat -> Fmt.string out "sat"
    | Unsat -> Fmt.string out "unsat"
    | Idle -> Fmt.string out "idle"
    | Conflict c -> Fmt.fprintf out "(@[conflict %a@])" Clause.pp c

  let pp_trail_elt out (k,lit) = match k with
    | Decision -> Fmt.fprintf out "%a*" Lit.pp lit
    | Prop _ -> Lit.pp out lit

  let pp out (self:t) : unit =
    Fmt.fprintf out
      "(@[st @[:status@ %a@]@ @[:cs@ (@[%a@])@]@ @[:trail@ (@[%a@])@]@])"
      pp_status self.status (pp_list Clause.pp) self.cs
      (pp_list pp_trail_elt) self.trail

  let parse : t P.t =
    let open P in
    (skip_white *> char '(' *> many Clause.parse <* skip_white <* char ')')
    >|= fun cs -> make cs [] Idle

  let eval_to_false (self:t) (c:Clause.t) : bool =
    let lazy assign = self._assign in
    List.for_all (fun l -> Lit.Map.get_or ~default:false (-l) assign) c

  let find_false (self:t) : Clause.t option =
    CCList.find_opt (eval_to_false self) self.cs

  let do_conflict (self:t) c : _ ATS.step =
    match self.trail with
    | [] ->
      One (make self.cs self.trail Unsat) (* unsat! *)
    | (Decision,lit)::trail' when lit> 0 ->
      (* backtrack, and make opposite decision *)
      One (make self.cs ((Decision, -lit) :: trail') Idle)
    | _::trail' ->
      (* backtrack further *)
      One (make self.cs trail' (Conflict c))

  let find_unit_c (self:t) : (Clause.t * Lit.t) option =
    let lazy assign = self._assign in
    Iter.of_list self.cs
    |> Iter.find_map
      (fun c ->
         (* non-false lits *)
         let lits = List.filter (fun l -> Lit.Map.get l assign <> Some false) c in
         match lits with
         | [l] when not (Lit.Map.mem l assign) -> Some (c,l)
         | _ -> None)

  let propagate self : _ ATS.step option =
    match find_unit_c self with
    | Some (c,l) ->
      Some (ATS.One (make self.cs ((Prop c,l)::self.trail) Idle))
    | None -> None

  let do_decision self : _ ATS.step =
    (* try to decide *)
    let lazy vars = self._to_decide in
    if Lit.Set.is_empty vars then (
      (* full model, we're done! *)
      ATS.Done (make self.cs self.trail Sat)
    ) else if Lit.Set.cardinal vars= 1 then (
      (* only one possible decision *)
      let v = Lit.Set.choose vars in
      ATS.One (make self.cs ((Decision,v) :: self.trail) Idle)
    ) else (
      (* multiple possible decisions *)
      let decs =
        Lit.Set.to_seq vars
        |> Iter.map (fun v -> make self.cs ((Decision,v) :: self.trail) Idle)
        |> Iter.to_rev_list
      in
      ATS.Choice decs
    )

  let do_idle self : _ ATS.step =
    match find_false self with
    | Some c ->
      (* conflict! *)
      One (make self.cs self.trail (Conflict c))
    | None ->
      match propagate self with
      | Some s -> s
      | None -> do_decision self

  (* main step function *)
  let next (self:t) : t ATS.step =
    match self.status with
    | Sat | Unsat -> ATS.Done self
    | Conflict c -> do_conflict self c
    | Idle -> do_idle self
end

module A = struct
  let name = "dpll"
  module State = State

  let next = State.next
end

let ats : ATS.t = (module A)
