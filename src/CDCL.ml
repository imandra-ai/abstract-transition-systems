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

module State = struct
  type trail_kind = Decision | Prop of Clause.t
  type trail_elt = trail_kind * Lit.t
  type trail = trail_elt list
  type status =
    | Sat
    | Unsat
    | Conflict of Clause.t
    | Backjump of Clause.t
    | Searching
  type t = {
    cs: Clause.t list;
    trail: trail;
    status: status;
    _lvl: int lazy_t;
    _all_vars: Lit.Set.t lazy_t;
    _to_decide: Lit.Set.t lazy_t;
    _assign: bool Lit.Map.t lazy_t; (* assignment, from trail *)
  }

  (* main constructor *)
  let make (cs:Clause.t list) (trail:trail) status : t =
    let _lvl = lazy
      Iter.(of_list trail
            |> filter (function (Decision,_) -> true | _ -> false) |> length)
      in
    let _all_vars = lazy (
      Iter.(of_list cs |> flat_map Clause.lits |> map Lit.abs) |> Lit.Set.of_seq;
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
    {cs;trail;status;_lvl; _all_vars; _to_decide; _assign}

  let empty : t = make [] [] Searching

  let pp_status out = function
    | Sat -> Fmt.string out "sat"
    | Unsat -> Fmt.string out "unsat"
    | Searching -> Fmt.string out "searching"
    | Conflict c -> Fmt.fprintf out "(@[conflict %a@])" Clause.pp c
    | Backjump c -> Fmt.fprintf out "(@[backjump %a@])" Clause.pp c

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
    (skip_white *> char '(' *>
     parsing "clause list" (many Clause.parse <* skip_white) <* char ')')
    >|= fun cs -> make cs [] Searching

  let eval_to_false (self:t) (c:Clause.t) : bool =
    let lazy assign = self._assign in
    Clause.for_all (fun l -> Lit.Map.get_or ~default:false (-l) assign) c

  let resolve_conflict_ (self:t) : _ ATS.step option =
    let open ATS in
    match self.status with
    | Conflict c when Clause.is_empty c ->
      Some (One (make self.cs self.trail Unsat, "learnt false"))
    | Conflict c ->
      begin match self.trail with
        | [] ->
          Some (One (make self.cs self.trail Unsat, "empty trail")) (* unsat! *)
        | (Prop d,lit)::trail' when Clause.contains (-lit) c ->
          (* resolution *)
          assert (Clause.contains lit d);
          let res = Clause.union (Clause.remove lit d) (Clause.remove (-lit) c) in
          let expl = Fmt.sprintf "resolve on %a with %a" Lit.pp lit Clause.pp d in
          Some (One (make self.cs trail' (Conflict res), expl))
        | (Prop _,_) :: trail' ->
          Some (One (make self.cs trail' self.status, "consume"))
        | (Decision, _) :: _ ->
          (* start backjumping *)
          Some (One (make self.cs self.trail (Backjump c), "backjump below conflict level"))
      end
    | _ -> None

  let backjump_ (self:t) : _ ATS.step option =
    let open ATS in
    match self.status with
    | Backjump c when Clause.is_empty c ->
      Some (One (make self.cs self.trail Unsat, "learnt false"))
    | Backjump c ->
      let rec unwind_trail trail =
        match trail with
        | [] -> 
          Some (One (make self.cs self.trail Unsat, "empty trail")) (* unsat! *)
        | (_,lit) :: _ when Clause.contains (-lit) c ->
          let tr = unwind_till_next_decision trail in
          let expl = Fmt.sprintf "backjump with %a" Clause.pp c in
          Some (One (make (c :: self.cs) ((Prop c,-lit)::tr) Searching, expl))
        | _::trail' -> unwind_trail trail'
      and unwind_till_next_decision = function
        | [] -> []
        | (Decision, _) :: tr -> tr
        | (Prop _, _) :: tr -> unwind_till_next_decision tr
      in
      unwind_trail self.trail
    | _ -> None

  let find_unit_c (self:t) : (Clause.t * Lit.t) option =
    let lazy assign = self._assign in
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
    | Some (c,l) ->
      let expl = Fmt.sprintf "propagate %a from %a" Lit.pp l Clause.pp c in
      Some (ATS.One (make self.cs ((Prop c,l)::self.trail) Searching, expl))
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
               make self.cs ((Decision,v) :: self.trail) Searching,
               Fmt.sprintf "decide %a" Lit.pp v
             in
             [mk_ v; mk_ (-v)])
        |> Iter.to_rev_list
      in
      Some (ATS.Choice decs)
    )

  let find_false (self:t) : _ option =
    match CCList.find_opt (eval_to_false self) self.cs with
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
  let name = "cdcl"
  module State = State

  let rules = State.rules
end

let ats : ATS.t = (module ATS.Make(A))
