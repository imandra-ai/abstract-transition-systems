module Fmt = CCFormat

module Vdom = struct
  include Vdom
  let h2 x = elt "h2" [text x]
  let pre x = elt "pre" [text x]
  let pre_f fmt = Fmt.ksprintf ~f:pre fmt
  let ul l = elt "ul" @@ List.map (fun x -> elt "li" [x]) l
  let button txt msg = input [] ~a:[onclick (fun _ -> msg); type_button; value txt]
  let div_class c x = elt "div" ~a:[class_ c] x

  let details ?short x =
    let open Vdom in
    let l = match short with None -> [x] | Some s -> [elt "summary" [text s]; x] in
    Vdom.(elt "details" l)
end

module type APP_CALCULUS = sig
  val name : string

  type msg
  type model

  val parse : string -> (model, string) result

  val init : model
  val view : model -> msg Vdom.vdom
  val update : model -> msg -> (model, string) result
end

module CDCL
  : APP_CALCULUS
= struct
  open Ats.CDCL
  module A = Ats.ATS.Make(Ats.CDCL.A)

  let name = "cdcl"
  type msg =
    | M_next
    | M_step
    | M_go_back of int

  type model = {
    parents: A.State.t list; (* parent states *)
    st: A.State.t; (* current state *)
    step: (A.State.t * string) Ats.ATS.step;
  }

  let init =
    let st = State.empty in
    { st; parents=[]; step=Ats.ATS.Done (st, ""); }

  let mk_ parents st =
    { st; parents; step=A.next st; }

  let parse (s:string) : _ result =
    match CCParse.parse_string State.parse s with
    | Error msg -> Error msg
    | Ok st -> Ok (mk_ [] st)

  let view_st (st:State.t) : msg Vdom.vdom =
    let open Vdom in
    let status, trail, cs = State.view st in
    div_class "ats-state" [
      pre (Fmt.sprintf "status: %a" State.pp_status status);
      details ~short:(Fmt.sprintf "trail (%d elts)" (Trail.length trail)) (
        Trail.to_iter trail
        |> Iter.mapi
          (fun i elt ->
             div [
               pre (Fmt.to_string Trail.pp_trail_elt elt);
               button "go" (M_go_back i);
             ])
        |> Iter.to_list |> ul |> CCList.return |> div_class "ats-trail"
      );
      details ~short:(Fmt.sprintf "clauses (%d)" (List.length cs)) (
        List.map (fun c -> pre_f "%a" Clause.pp c) cs |> div_class "ats-clauses"
      );
    ]

  let view (m: model) : _ Vdom.vdom =
    let open Vdom in
    let v_actions = match m.step with
      | Ats.ATS.One _ | Ats.ATS.Done _ | Ats.ATS.Error _ ->
        [button "step" M_step; button "next" M_next]
      | Ats.ATS.Choice _ ->
        [button "step" M_step]
    and v_lm = [
      let view_parent i st =
        div [
          view_st st;
          button "go" (M_go_back i);
        ]
      in
      div @@ List.flatten [
        [h2 name];
        (if m.parents=[] then []
         else [
           details ~short:(Printf.sprintf "previous (%d)" (List.length m.parents))
             (div_class "ats-parents"
                [ul @@ List.rev (List.mapi view_parent m.parents)])]);
        [view_st m.st]
      ];
    ] in
    div @@ List.flatten [v_actions; v_lm]

  let update (m:model) (msg:msg) : _ result =
    let {parents; st; step } = m in
    match msg with
    | M_next ->
      begin match step with
        | Ats.ATS.Done (st',_) ->
          Ok (mk_ parents st') (* just go to [st'] *)
        | Ats.ATS.Error msg ->
          Error msg
        | Ats.ATS.One (st',_) | Ats.ATS.Choice [st',_] ->
          Ok (mk_ (st::parents) st')
        | Ats.ATS.Choice _ ->
          Error "need to make a choice"
      end
    | M_step ->
      begin match step with
        | Ats.ATS.Done (st',_) -> Ok (mk_ parents st')
        | Ats.ATS.Error msg -> Error msg
        | Ats.ATS.One (st',_) | Ats.ATS.Choice ((st',_)::_) ->
          Ok (mk_ (st::parents) st') (* make a choice *)
        | Ats.ATS.Choice _ -> assert false
      end
    | M_go_back i ->
      begin try
          let st = List.nth parents i in
          Ok (mk_ (CCList.drop (i+1) parents) st)
        with _ -> Error "invalid index in parents"
      end
end

(* TODO
module MCSAT = struct
  module A = Ats.ATS.Make(Ats.MCSAT.A)
  let view (_st:A.State.t) =
  assert false
  end
   *)

module App = struct
  open Vdom

  type msg =
    | M_load of string
    | M_set_parse of string
    | M_parse
    | M_cdcl of CDCL.msg

  type logic_model =
    | LM_cdcl of CDCL.model
      
  type model = {
    error: string option;
    parse: string;
    lm: logic_model;
  }

  let all = ["cdcl"; "mcsat"]
  let init_ s : logic_model =
    match s with
    | "cdcl" -> LM_cdcl CDCL.init
    | "mcsat" ->
      assert false (* TODO *)
    | s -> failwith @@ "unknown system " ^ s

  let init : model =
    { error=None; parse=""; lm=init_ "cdcl";
    }

  let update (m:model) (msg:msg) =
    match msg, m with
    | M_load s, _ -> {error=None; lm=init_ s; parse=""}
    | M_set_parse s, _ -> {m with parse=s}
    | M_parse, {parse=s; lm; _} ->
      let lm' = match lm with
        | LM_cdcl _ -> CDCL.parse s |> CCResult.map (fun m -> LM_cdcl m)
      in
      begin match lm' with
        | Ok lm' -> {m with error=None; lm=lm'}
        | Error msg ->
          {m with error=Some msg}
      end
    | M_cdcl msg, {lm=LM_cdcl u;_} ->
      begin match CDCL.update u msg with
        | Ok lm -> {m with error=None; lm=LM_cdcl lm}
        | Error msg -> {m with error=Some msg}
      end
      (* TODO
    | M_cdcl _, _ -> {m with error=Some "invalid message for CDCL";}
         *)

  let view (m:model) =
    let {error; parse; lm} = m in
    let v_error = match error with
      | None -> []
      | Some s -> [div ~a:[style "color" "red"] [text s]]
    and v_load = [ 
      ul @@ List.map (fun s -> button ("load " ^ s) (M_load s)) all;
    ]
    and v_parse = [
      div [
        input [] ~a:[type_ "text"; value parse; oninput (fun s -> M_set_parse s)];
        button "parse" M_parse;
      ]
    ]
    and v_lm = match lm with
      | LM_cdcl m ->
        [CDCL.view m |> map (fun x -> M_cdcl x)]
    in
    div @@ List.flatten [v_error; v_load; v_parse; v_lm]

  let app = Vdom.simple_app ~init ~update ~view ()
end

open Js_browser

let run () = Vdom_blit.run App.app |> Vdom_blit.dom |> Element.append_child (Document.body document)
let () = Window.set_onload window run
