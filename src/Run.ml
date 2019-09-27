open Util

module L = Run_intf.L
module type S = Run_intf.S

module Make(A: ATS.S) = struct
  module A = A

  module Transition = struct
    type t = {
      init: A.State.t;
      final: A.State.t;
      expl: expl;
    }
    and expl =
      | Choice of int * string
      | Deterministic of string
      | Multi_deterministic of t list (* aggregate of deterministic transitions *)

    let make init final expl : t = {init;final;expl}
    let make_deter init final expl = make init final (Deterministic expl)
    let make_choice init final i expl = make init final (Choice (i, expl))

    let rec pp out (s:t) : unit =
      Fmt.fprintf out
        "(@[transition@ @[<2>:from@ %a@]@ @[<2>:to@ %a@]@ @[<2>:expl %a@]@])"
        A.State.pp s.init A.State.pp s.final pp_expl s.expl

    and pp_expl out = function
      | Choice (i, s) ->
        Fmt.fprintf out "(@[@{<yellow>choice@} %d@ by %S@])" i s
      | Deterministic s ->
        Fmt.fprintf out "(@[@{<green>deterministic@} by %S@])" s
      | Multi_deterministic ([] | [_]) -> assert false
      | Multi_deterministic l ->
        Fmt.fprintf out "(@[<hv2>@{<green>multi-step@}[%d]@ %a@])"
          (List.length l) (pp_list pp) l

    (** append the lists, possibly merging last entry of [l1] and first entry of [l2] *)
    let append_l (l1: t L.t) (l2:t L.t) : t L.t =
      match List.rev l1, l2 with
      | last_l1 :: l1', first_l2 :: l2' ->
        let l1' = List.rev l1' in
        (* merge last of l1, and first of l2 *)
        let merge = match last_l1.expl, first_l2.expl with
          | Deterministic _, Deterministic _ ->
            [{init=last_l1.init; final=first_l2.final;
              expl=Multi_deterministic [last_l1; first_l2]}]
          | Deterministic _, Multi_deterministic d2 ->
            [{init=last_l1.init; final=first_l2.final;
              expl=Multi_deterministic (last_l1 :: d2)}]
          | Multi_deterministic d1, Deterministic _ ->
            [{init=last_l1.init; final=first_l2.final;
              expl=Multi_deterministic (d1 @ [first_l2])}]
          | Multi_deterministic d1, Multi_deterministic d2 ->
            [{init=last_l1.init; final=first_l2.final;
              expl=Multi_deterministic (d1 @ d2)}]
          | _ -> [last_l1; first_l2]
        in
        CCList.flatten [l1'; merge; l2']
      | _ -> CCList.append l1 l2
  end

  module Trace = struct
    type status =
      | Active
      | Stopped
      | Error of string
    type t = {
      init: A.State.t;
      final: A.State.t;
      status: status;
      transitions: Transition.t L.t;
    }

    let transitions st = Iter.of_list st.transitions
    let trivial st : t = {init=st; final=st; status=Active; transitions=[]}
    let is_done_status = function Active -> false | Stopped | Error _ -> true
    let is_done tr = is_done_status tr.status

    let append (tr1:t) (tr2:t) : t =
      if tr1.status = Active then (
        let transitions=Transition.append_l tr1.transitions tr2.transitions in
        { init=tr1.init; final=tr2.final; status=tr2.status; transitions; }
      ) else tr1

    let pp out (tr:t) : unit =
      Fmt.fprintf out
        "(@[trace%s@ @[<2>:init@ %a@]@ @[<2>:final@ %a@]@ @[<hv2>:transitions@ %a@]@])"
        (match tr.status with Active-> "" | Stopped -> "[stopped]" | Error _ -> "[error]")
        A.State.pp tr.init A.State.pp tr.final
        (pp_list Transition.pp) tr.transitions

    module Infix = struct
      let (<+>) = append
    end
    include Infix
  end

  module Tactic = struct
    type t =
      | Auto of int
      | Next of int (* only follow deterministic transitions and unique choices *)

    let pp out = function
      | Auto 1 -> Fmt.string out "auto"
      | Auto i -> Fmt.fprintf out "(auto %d)" i
      | Next 1 -> Fmt.string out "next"
      | Next i -> Fmt.fprintf out "(next %d)" i
  end

  type choice = (A.State.t * string) list

  type tmp_st = {
    mutable cur_st : A.State.t;
    mutable status: Trace.status;
    mutable choices: choice option;
    mutable trace: Transition.t list;
  }

  let call_next_once_ st : unit =
    match A.next st.cur_st with
    | ATS.Done ->
      st.status <- Trace.Stopped;
    | ATS.Error msg ->
      st.status <- Trace.Error msg;
    | ATS.One (st', expl) ->
      st.trace <- Transition.make_deter st.cur_st st' expl :: st.trace;
      st.cur_st <- st';
    | ATS.Choice [(st', expl)] ->
      st.trace <- Transition.make_choice st.cur_st st' 1 expl :: st.trace;
      st.cur_st <- st';
    | ATS.Choice [] ->
      st.status <- Trace.Error "dead end: empty choice list"
    | ATS.Choice l ->
      st.choices <- Some l

  (* run [A.next] at most [i] times, but stop if it finishes or a choice
     must be made. *)
  let rec do_next st i =
    match st.status with
    | Trace.Error _ | Trace.Stopped -> ()
    | _ when i<=0 -> ()
    | Trace.Active ->
      call_next_once_ st;
      if not (Trace.is_done_status st.status) && CCOpt.is_none st.choices then (
        do_next st (i-1)
      )

  let rec do_auto (st:tmp_st) i : unit =
    let auto_choice = function
      | [] -> assert false
      | (st',expl) :: _ ->
        st.trace <- Transition.make_choice st.cur_st st' 1 expl :: st.trace;
        st.choices <- None;
        st.cur_st <- st';
    in
    begin match st.choices with
      | _ when i<0 -> ()
      | _ when Trace.is_done_status st.status -> ()
      | None ->
        (* do one step of [next], with automatic choice if needed *)
        call_next_once_ st;
        (do_auto [@tailcall]) st (i-1)
      | Some [] ->
        st.status <- Error "dead end: no possible choice"
      | Some l ->
        auto_choice l;
        (do_auto [@tailcall]) st (i-1)
    end

  let run (tactic:Tactic.t) (st0:A.State.t) : _ * _ =
    let st = { trace=[]; cur_st=st0; choices=None; status=Trace.Active } in
    begin match tactic with
      | Tactic.Next n -> do_next st n
      | Tactic.Auto n -> do_auto st n
    end;
    (* produce a trace from [st] *)
    let trace = {
      Trace.
      init=st0; final=st.cur_st;
      transitions=List.rev st.trace;
      status=st.status;
    } in
    trace, st.choices
end
