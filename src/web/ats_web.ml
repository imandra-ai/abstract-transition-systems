module Fmt = CCFormat

module App = struct
  open Vdom

  type msg =
    | M_load of string
    | M_parse
    | M_set_parse of string
    | M_next
    | M_step

  let h2 x = elt "h2" [text x]
  let pre x = elt "pre" [text x]
  let pre_f fmt = Fmt.ksprintf ~f:pre fmt
  let ul l = elt "ul" @@ List.map (fun x -> elt "li" [x]) l
  let button txt msg = input [] ~a:[onclick (fun _ -> msg); type_button; value txt]

  let details ?short x =
    let open Vdom in
    let l = match short with None -> [x] | Some s -> [elt "summary" [text s]; x] in
    Vdom.(elt "details" l)

  module type ATS = sig
    module A : Ats.ATS.S
    val view : A.State.t -> msg Vdom.vdom
  end

  module CDCL = struct
    module A = Ats.ATS.Make(Ats.CDCL.A)
    open Ats.CDCL
    let view (st:A.State.t) =
      let status, trail, cs = State.view st in
      div [
        pre (Fmt.sprintf "status: %a" State.pp_status status);
        details ~short:(Fmt.sprintf "trail (%d elts)" (Trail.length trail)) (
          Trail.to_iter trail
          |> Iter.map
            (fun elt -> pre (Fmt.to_string Trail.pp_trail_elt elt))
          |> Iter.to_list |> ul
        );
        details ~short:(Fmt.sprintf "clauses (%d)" (List.length cs)) (
          List.map (fun c -> pre_f "%a" Clause.pp c) cs |> ul
        );
      ]
  end

  module MCSAT = struct
    module A = Ats.ATS.Make(Ats.MCSAT.A)
    let view (_st:A.State.t) =
      assert false
  end

  type 'a ats = (module ATS with type A.State.t = 'a)

  type logic_model =
    | LM : {
        ats: 'st ats;
        parents: 'st list; (* parent states *)
        st: 'st; (* current state *)
        step: ('st * string) Ats.ATS.step;
    } -> logic_model
      
  type model = {
    error: string option;
    parse: string;
    lm: logic_model;
  }

  let all = ["cdcl"; "mcsat"]
  let init_ s : logic_model =
    match s with
    | "cdcl" ->
      let st = CDCL.A.State.empty in
      LM { ats=(module CDCL); st; parents=[]; step=Ats.ATS.Done (st, ""); }
    | "mcsat" ->
      let st = CDCL.A.State.empty in
      LM { ats=(module CDCL); st; parents=[]; step=Ats.ATS.Done (st, ""); }
    | s -> failwith @@ "unknown system " ^ s

  let init : model =
    { error=None; parse=""; lm=init_ "cdcl";
    }

  let update (m:model) (msg:msg) =
    match msg, m with
    | M_load s, _ -> {error=None; lm=init_ s; parse=""}
    | M_set_parse s, _ -> {m with parse=s}
    | M_parse, {parse; lm=LM ({ats=(module A); _} as a); _} ->
      begin match CCParse.parse_string A.A.State.parse parse with
        | Ok st ->
          let step = A.A.next st in
          {m with lm=LM {a with st; step; }}
        | Error msg ->
          {m with error=Some msg}
      end
    | M_next, {lm=LM ({ats=(module A); st; step; _} as a); _} ->
      begin match step with
        | Ats.ATS.Done (st',_) ->
          {m with lm=LM {a with st=st'; }} (* just go to [st'] *)
        | Ats.ATS.Error msg ->
          {m with error=Some msg}
        | Ats.ATS.One (st',_) | Ats.ATS.Choice [st',_] ->
          {m with lm=LM {a with st=st'; parents=st::a.parents; step=A.A.next st'}}
        | Ats.ATS.Choice _ ->
          {m with error=Some "need to make a choice"}
      end
    | M_step, {lm=LM ({ats=(module A); st; step; _} as a); _} ->
      begin match step with
        | Ats.ATS.Done (st',_) ->
          {m with lm=LM {a with st=st'; }} (* just go to [st'] *)
        | Ats.ATS.Error msg ->
          {m with error=Some msg}
        | Ats.ATS.One (st',_) | Ats.ATS.Choice ((st',_)::_) ->
          (* make a choice *)
          {m with lm=LM {a with st=st'; parents=st::a.parents; step=A.A.next st'}}
        | Ats.ATS.Choice _ -> assert false
      end

  let view (m:model) =
    let {error; parse; lm=LM ({ats=(module A); step; _} as a)} = m in
    let v_error = match error with
      | None -> []
      | Some s -> [div ~a:[style "color" "red"] [text s]]
    and v_load = [ 
      ul @@ List.map (fun s -> button ("load " ^ s) (M_load s)) all;
    ]
    and v_actions = match step with
      | Ats.ATS.One _ | Ats.ATS.Done _ | Ats.ATS.Error _ ->
        [button "next" M_next; button "step" M_step]
      | Ats.ATS.Choice _ ->
        [button "step" M_step]
    and v_parse = [
      div [
        input [] ~a:[type_ "text"; value parse; oninput (fun s -> M_set_parse s)];
        button "parse" M_parse;
      ]
    ]
    in
    let v_lm = [
      div @@ List.flatten [
        [h2 A.A.name];
        (if a.parents=[] then []
         else [
               details ~short:(Printf.sprintf "previous (%d)" (List.length a.parents))
               (div (List.rev_map A.view a.parents))]);
        [A.view a.st]
      ];
    ] in
    div @@ List.flatten [v_error; v_load; v_parse; v_actions; v_lm]

  let app = Vdom.simple_app ~init ~update ~view ()
end

open Js_browser

let run () = Vdom_blit.run App.app |> Vdom_blit.dom |> Element.append_child (Document.body document)
let () = Window.set_onload window run
