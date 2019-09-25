module Fmt = CCFormat

module Vdom = struct
  include Vdom
  let h2 x = elt "h2" [text x]
  let pre x = elt "pre" [text x]
  let pre_f fmt = Fmt.ksprintf ~f:pre fmt
  let ul l = elt "ul" @@ List.map (fun x -> elt "li" [x]) l
  let button txt msg = input [] ~a:[onclick (fun _ -> msg); type_button; value txt]
  let div_class c x = elt "div" ~a:[class_ c] x
  let color s = style "color" s
  let text_f fmt = Fmt.ksprintf ~f:text fmt
  let button_f act fmt = Fmt.ksprintf ~f:(fun x -> button x act) fmt

  let details ?short x =
    let open Vdom in
    let l = match short with None -> [x] | Some s -> [elt "summary" [text s]; x] in
    Vdom.(elt "details" l)
end

module Calculus_msg = struct
  type t =
    | M_next
    | M_step
    | M_pick of int
    | M_go_back of int
end

module type APP_CALCULUS = sig
  val name : string

  type msg = Calculus_msg.t
  type model

  val parse : string -> (model, string) result

  val init : model
  val view : model -> msg Vdom.vdom
  val update : model -> msg -> (model, string) result
end

module type CALCULUS = sig
  module A : Ats.ATS.S
  val name : string
  val view : A.State.t -> Calculus_msg.t Vdom.vdom
end

module Make_calculus(C : CALCULUS)
  : APP_CALCULUS
= struct
  open C.A
  open Calculus_msg

  let name = C.name

  type msg = Calculus_msg.t
  type model = {
    parents: (State.t * string) list; (* parent states *)
    st: State.t; (* current state *)
    step: (State.t * string) Ats.ATS.step;
  }

  let init =
    let st = State.empty in
    { st; parents=[]; step=Ats.ATS.Done (st, ""); }

  let mk_ parents st =
    { st; parents; step=next st; }

  let parse (s:string) : _ result =
    match CCParse.parse_string State.parse s with
    | Error msg -> Error msg
    | Ok st -> Ok (mk_ [] st)

  let view (m: model) : _ Vdom.vdom =
    let open Vdom in
    let v_actions_pre, v_actions_post = match m.step with
      | Ats.ATS.Done _ | Ats.ATS.Error _ ->
        [button "step" M_step; button "next" M_next], []
      | Ats.ATS.One (_,expl) ->
        [button "step" M_step; div [button "next" M_next; text_f "(by: %s)" expl]], []
      | Ats.ATS.Choice l ->
        let choices =
          List.mapi
            (fun i (st,expl) ->
               div_class "ats-choice"
                 [C.view st; button "pick" (M_pick i); text_f "(%s)" expl; ])
            l
        in
        [button "step" M_step], [h2 "choices:"; div_class "ats-choices" choices]
    and v_parents =
      let view_parent i (st,expl) =
        div_class "ats-parent" [
          C.view st;
          button "go back" (M_go_back i);
          text_f "(next: %s)" expl;
        ]
      in
      if m.parents=[] then []
       else [
         details ~short:(Printf.sprintf "previous (%d)" (List.length m.parents))
           (div_class "ats-parents" @@ List.mapi view_parent m.parents)]
    in
    div @@ List.flatten [
      [h2 name];
      v_actions_pre;
      [C.view m.st];
      v_actions_post;
      v_parents;
    ]

  let update (m:model) (msg:msg) : _ result =
    let {parents; st; step } = m in
    match msg with
    | M_next ->
      begin match step with
        | Ats.ATS.Done (st',_) ->
          Ok (mk_ parents st') (* just go to [st'] *)
        | Ats.ATS.Error msg ->
          Error msg
        | Ats.ATS.One (st',expl) | Ats.ATS.Choice [st',expl] ->
          Ok (mk_ ((st,expl)::parents) st')
        | Ats.ATS.Choice _ ->
          Error "need to make a choice"
      end
    | M_step ->
      begin match step with
        | Ats.ATS.Done (st',_) -> Ok (mk_ parents st')
        | Ats.ATS.Error msg -> Error msg
        | Ats.ATS.One (st',expl) | Ats.ATS.Choice ((st',expl)::_) ->
          Ok (mk_ ((st,expl)::parents) st') (* make a choice *)
        | Ats.ATS.Choice _ -> assert false
      end
    | M_pick i ->
      begin match step with
        | Ats.ATS.Choice l ->
          begin try
              let st', expl = List.nth l i in
              Ok (mk_ ((st,expl)::parents) st')
            with _ -> Error "invalid `pick`"
          end
        | _ -> Error "cannot pick a state, not in a choice state"
      end
    | M_go_back i ->
      begin try
          let st, _expl = List.nth parents i in
          Ok (mk_ (CCList.drop (i+1) parents) st)
        with _ -> Error "invalid index in parents"
      end
end

module CDCL = Make_calculus(struct
    module A = Ats.ATS.Make(Ats.CDCL.A)
    open Ats.CDCL
    open Calculus_msg

    let name = "cdcl"
    let view (st:State.t) : Calculus_msg.t Vdom.vdom =
      let open Vdom in
      let status, trail, cs = State.view st in
      div_class "ats-state" [
        pre (Fmt.sprintf "status: %a" State.pp_status status);
        details ~short:(Fmt.sprintf "trail (%d elts)" (Trail.length trail)) (
          Trail.to_iter trail
          |> Iter.map
            (fun elt -> pre (Fmt.to_string Trail.pp_trail_elt elt))
          |> Iter.to_list |> div_class "ats-trail"
        );
        details ~short:(Fmt.sprintf "clauses (%d)" (List.length cs)) (
          List.map (fun c -> pre_f "%a" Clause.pp c) cs |> div_class "ats-clauses"
        );
      ]
  end)

module MCSAT = Make_calculus(struct
    module A = Ats.ATS.Make(Ats.MCSAT.A)
    open Ats.MCSAT
    open Calculus_msg

    let name = "mcsat"
    let view (st:State.t) : Calculus_msg.t Vdom.vdom =
      let open Vdom in
      let status, cs, trail, env = State.view st in
      div_class "ats-state" [
        pre (Fmt.sprintf "status: %a" State.pp_status status);
        details ~short:(Fmt.sprintf "trail (%d elts)" (Trail.length trail)) (
          Trail.to_iter trail
          |> Iter.map (fun elt -> pre_f "%a" Trail.pp_trail_elt elt)
          |> Iter.to_list |> div_class "ats-trail"
        );
        details ~short:(Fmt.sprintf "clauses (%d)" (Clause.Set.cardinal cs))
          (Clause.Set.elements cs |> List.map (fun c -> pre_f "%a" Clause.pp c)
           |> div_class "ats-clauses"
        );
        details ~short:(Fmt.sprintf "env (%d)" (Env.length env))
          (Env.to_iter env
           |> Iter.map (fun c -> pre_f "%a" Env.pp_item c) |> Iter.to_list
           |> div_class "ats-clauses"
        );
      ]
  end)

module App = struct
  open Vdom

  type msg =
    | M_load of string
    | M_set_parse of string
    | M_parse
    | M_calculus of Calculus_msg.t
    | M_and_then of msg * msg

  type logic_model =
    | LM : {
        app: (module APP_CALCULUS with type model = 'm);
        model: 'm;
      } -> logic_model
      
  type model = {
    error: string option;
    parse: string;
    lm: logic_model;
  }

  let all_ = [
    "cdcl", LM { app=(module CDCL); model=CDCL.init; };
    "mcsat", LM { app=(module MCSAT); model=MCSAT.init; }
  ]

  let init : model =
    { error=None; parse=""; lm=List.assoc "mcsat" all_; }

  let rec update (m:model) (msg:msg) : model =
    match msg, m with
    | M_load s, _ ->
      begin
        try let f = List.assoc s all_ in {error=None; lm=f; parse=""}
        with Not_found -> {m with error=Some (Printf.sprintf "unknown system %s" s)}
      end
    | M_set_parse s, _ -> {m with parse=s}
    | M_parse, {parse=s; lm; _} ->
      let lm' = match lm with
        | LM {app=(module App) as app; _} ->
          App.parse s |> CCResult.map (fun m -> LM {app; model=m})
      in
      begin match lm' with
        | Ok lm' -> {m with error=None; lm=lm'}
        | Error msg ->
          {m with error=Some msg}
      end
    | M_calculus msg, {lm=LM {app=(module App) as app; model};_} ->
      begin match App.update model msg with
        | Ok lm -> {m with error=None; lm=LM {app; model=lm}}
        | Error msg -> {m with error=Some msg}
      end
    | M_and_then (m1,m2), _ -> update (update m m1) m2

  let view (m:model) =
    let {error; parse; lm} = m in
    let v_error = match error with
      | None -> []
      | Some s -> [div ~a:[color "red"] [text s]]
    and v_load = [ 
      ul @@ List.map (fun (s,_) -> button ("use " ^ s) (M_load s)) all_;
    ]
    and v_load_parse_example = [
      List.map
        (fun (name,s) ->
           button_f (M_and_then (M_set_parse s, M_parse)) "load %S" name)
        Ats_examples.all
      |> div_class "ats-parse-examples"
    ]
    and v_parse = [
      div [
        input [] ~a:[type_ "text"; value parse; oninput (fun s -> M_set_parse s)];
        button "parse" M_parse;
      ]
    ]
    and v_lm = match lm with
      | LM {app=(module App); model} ->
        [App.view model |> map (fun x -> M_calculus x)]
    in
    div_class "ats" @@ List.flatten [
      v_error; v_load; v_load_parse_example; v_parse; v_lm;
    ]

  let app = Vdom.simple_app ~init ~update ~view ()
end

open Js_browser

let run () = Vdom_blit.run App.app |> Vdom_blit.dom |> Element.append_child (Document.body document)
let () = Window.set_onload window run
