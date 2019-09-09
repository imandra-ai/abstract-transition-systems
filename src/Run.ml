open Util

module L = Run_intf.L
module type S = Run_intf.S

module Make(A: ATS.S) = struct
  module A = A
  module Cmd0 = struct
    type t =
      | Quit
      | Auto of int
      | Next of int
      | Show
      | Help of string option
      | Pick of int
      | Init of A.State.t
  end

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
    type t = {
      init: A.State.t;
      final: (A.State.t, string) result;
      stopped: bool;
      transitions: Transition.t list;
    }

    let transitions st = Iter.of_list st.transitions
    let trivial st : t = {init=st; final=Ok st; stopped=false; transitions=[]}

    let append (tr1:t) (tr2:t) : t =
      if tr1.stopped then tr1
      else (
        let transitions=Transition.append_l tr1.transitions tr2.transitions in
        { init=tr1.init; final=tr2.final; stopped= tr2.stopped; transitions; }
      )

    let pp out (tr:t) : unit =
      Fmt.fprintf out
        "(@[trace%s@ @[<2>:init@ %a@]@ @[<2>:final@ %a@]@ @[<hv2>:transitions@ %a@]@])"
        (if tr.stopped then "[stopped]" else "")
        A.State.pp tr.init (Fmt.Dump.result A.State.pp) tr.final
        (pp_list Transition.pp) tr.transitions

    module Infix = struct
      let (<+>) = append
    end
    include Infix
  end

  let run (_cmd:Cmd0.t) (_st:A.State.t) : Trace.t =
    assert false (* TODO *)
end
