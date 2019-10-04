module Fmt = CCFormat

module Vdom = struct
  include Vdom
  let h2 ?a x = elt ?a "h2" [text x]
  let h3 ?a x = elt ?a "h3" [text x]
  let h4 ?a x = elt ?a "h4" [text x]
  let h5 ?a x = elt ?a "h5" [text x]
  let pre ?a x = elt ?a "pre" [text x]
  let pre_f ?a fmt = Fmt.ksprintf ~f:(pre ?a) fmt
  let bold x = elt "bold" [x]
  let section cls x = elt "section" ~a:[class_ cls] x
  let button ?cls ?(a=[]) txt msg =
    let a = match cls with None -> a | Some c -> class_ c :: a in
    input [] ~a:(onclick (fun _ -> msg) :: type_button :: value txt :: a)
  let button_f ?cls ?a act fmt =
    Fmt.ksprintf ~f:(fun x -> button ?cls ?a x act) fmt
  let div_class ?(a=[]) c x = elt "div" ~a:(class_ c::a) x
  let color s = style "color" s
  let text_f fmt = Fmt.ksprintf ~f:text fmt
  let id s = str_prop "id" s
  let title s = str_prop "title" s
  let title_f fmt = Fmt.ksprintf ~f:title fmt
  let on_key_enter ~default m = onkeydown (function {which=13} -> m | _ -> default)

  let details ?a ?(open_=false) ?short x =
    let open Vdom in
    let l = match short with None -> [x] | Some s -> [elt ?a "summary" [text s]; x] in
    let a = if open_ then [str_prop "open" "true"] else [] in
    elt ~a "details" l
end

module Calculus_msg = struct
  type t =
    | M_next
    | M_multi_next
    | M_step
    | M_auto of int
    | M_pick of int
    | M_go_back of int
end

module type APP_CALCULUS = sig
  val name : string

  type msg = Calculus_msg.t
  type model
  val kinds : Ats_examples.kind list

  val parse : string -> (model, string) result

  val init : model
  val view : model -> msg Vdom.vdom
  val update : model -> msg -> (model, string) result
end

module type CALCULUS = sig
  module A : Ats.ATS.S
  val name : string
  val kinds : Ats_examples.kind list
  val view : A.State.t -> Calculus_msg.t Vdom.vdom
end

let help_multinext = "recursively follow deterministic transitions"
let help_step = "follow one deterministic transition, or make one arbitrary choice"
let help_auto = "do `step` n times\n(automatic choices + deterministic transitions)"
let help_go_back = "go back to given state"

module Make_calculus(C : CALCULUS)
  : APP_CALCULUS
= struct
  open C.A
  open Calculus_msg

  let kinds = C.kinds
  let name = C.name

  type transition_kind = TK_pick | TK_one
  type msg = Calculus_msg.t
  type model = {
    parents: (State.t * Ats.ATS.is_decision * transition_kind * string) list; (* parent states *)
    st: State.t; (* current state *)
    step: (State.t lazy_t * Ats.ATS.is_decision * string) Ats.ATS.step lazy_t;
  }

  let init =
    let st = State.empty in
    { st; parents=[]; step=lazy Ats.ATS.Done; }

  let mk_ parents (st:State.t) =
    { st; parents; step=lazy (next st); }

  let parse (s:string) : _ result =
    match Ats.Sexp_parser.parse_string_str State.parse s with
    | Error msg -> Error msg
    | Ok st -> Ok (mk_ [] st)

  let view_ (m: model) : _ Vdom.vdom =
    let open Vdom in
    let v_actions_pre, v_actions_post =
      match Lazy.force m.step with
      | Ats.ATS.Done -> [], []
      | Ats.ATS.Error msg ->
        [button ~cls:"ats-button" ~a:[title help_step] "step" M_step;
         button ~cls:"ats-button" ~a:[title_f "error: %s" msg] "next" M_next],
        []
      | Ats.ATS.One (_,_,expl) ->
        [button ~cls:"ats-button" ~a:[title help_step] "step" M_step;
         button ~cls:"ats-button" ~a:[title expl] "next" M_next;
         button ~cls:"ats-button" ~a:[title help_multinext] "next*" M_multi_next], []
      | Ats.ATS.Choice l ->
        let choices =
          List.mapi
            (fun i (lazy st,_,expl) ->
               div_class "ats-choice"
                 [C.view st;
                  button ~cls:"ats-button" "pick" (M_pick i);
                  pre_f "(%s)" expl; ])
            l
        in
        [button ~cls:"ats-button" ~a:[title help_step] "step" M_step],
        [h2 "choices:"; div_class "ats-choices" choices]
    and v_parents =
      let n = List.length m.parents in
      let view_parent i (st,_is_dec,k,expl) = [
        (let k = match k with TK_one -> "→" | TK_pick -> "?" in
         div_class "ats-expl" [pre_f "%s %s" k expl]);
        div_class "ats-parent" [
          pre_f "[%d]" (n-i-1); 
          div ~key:(Printf.sprintf "parent-%d" (n-i)) [C.view st];
          button ~cls:"ats-button ats-button--goback"
            ~a:[title help_go_back] "go back" (M_go_back i);
        ];
      ]
      in
      if n=0 then []
      else (
        let n_dec = CCList.count (fun (_,is_dec,_,_) -> is_dec) m.parents in
        [div_class "ats-group--previous"
              [details ~open_:true
                 ~short:(Printf.sprintf "previous (%d, %d decs)" n n_dec)
                 (div_class "ats-parents"
                  @@ List.flatten @@ List.mapi view_parent m.parents)]]
      )
    in
    div_class "ats-group" @@ List.flatten [
      [h2 name];
      v_actions_pre;
      [div ~key:"ats-state" [C.view m.st]];
      v_actions_post;
      [div ~key:"ats-parents" @@ v_parents];
    ]

  let view m = Vdom.memo view_ m

  let do_step m =
    let {parents; st; step } = m in
    match Lazy.force step with
    | Ats.ATS.Done -> Error "done"
    | Ats.ATS.Error msg -> Error msg
    | Ats.ATS.One (lazy st',is_dec,expl) ->
      Ok (mk_ ((st,is_dec,TK_one,expl)::parents) st')
    | Ats.ATS.Choice ((lazy st',is_dec,expl)::_) ->
      Ok (mk_ ((st,is_dec,TK_pick,expl)::parents) st') (* make a choice *)
    | Ats.ATS.Choice _ -> assert false

  let rec do_auto n m =
    match Lazy.force m.step with
    | Done -> Ok m
    | _ when n <= 0 -> Ok m
    | _ ->
      match do_step m with
      | Error e -> Error e
      | Ok m' -> do_auto (n-1) m'

  (* follow any number of deterministic transitions *)
  let rec do_multi_next m =
    let {parents; st; step } = m in
    match Lazy.force step with
    | Error msg -> Error msg
    | Done -> Ok m
    | One (lazy st',is_dec,expl) | Choice [lazy st',is_dec,expl] ->
      do_multi_next (mk_ ((st,is_dec,TK_one,expl) :: parents) st')
    | _ -> Ok m

  let update (m:model) (msg:msg) : _ result =
    let {parents; st; step } = m in
    match msg with
    | M_next ->
      begin match Lazy.force step with
        | Done  -> Error "done"
        | Error msg -> Error msg
        | One (lazy st',is_dec,expl) | Choice [lazy st',is_dec,expl] ->
          Ok (mk_ ((st,is_dec,TK_one,expl)::parents) st')
        | Choice _ ->
          Error "need to make a choice"
      end
    | M_multi_next -> do_multi_next m
    | M_step -> do_step m
    | M_auto n -> do_auto n m
    | M_pick i ->
      begin match Lazy.force step with
        | Ats.ATS.Choice l ->
          begin try
              let lazy st', is_dec, expl = List.nth l i in
              Ok (mk_ ((st,is_dec, TK_pick,expl)::parents) st')
            with _ -> Error "invalid `pick`"
          end
        | _ -> Error "cannot pick a state, not in a choice state"
      end
    | M_go_back i ->
      begin try
          let st, _, _, _expl = List.nth parents i in
          Ok (mk_ (CCList.drop (i+1) parents) st)
        with _ -> Error "invalid index in parents"
      end
end

let h_status ?(a=[]) x = Vdom.(h5 ~a:(class_ "ats-status"::a) x)
let pre_trail ?(a=[]) x = Vdom.(pre ~a:(class_ "ats-trail"::a) x)
let pre_trail_f ?(a=[]) fmt = Vdom.(pre_f ~a:(class_ "ats-trail"::a) fmt)

module DPLL = Make_calculus(struct
    module A = Ats.ATS.Make(Ats.DPLL.A)
    open Ats.DPLL
    open Calculus_msg

    let kinds = [Ats_examples.K_cnf]
    let name = "dpll"
    let view (st:State.t) : Calculus_msg.t Vdom.vdom =
      let open Vdom in
      let status, trail, cs = State.view st in
      div_class "ats-state" [
        div_class "ats-status" [h_status "status: "; pre (Fmt.to_string State.pp_status status)];
        details ~short:(Fmt.sprintf "trail (%d elts)" (List.length trail))
          ~a:[title_f "@[<v>%a@]" State.pp_trail trail]
          (Iter.of_list trail
          |> Iter.map
            (fun elt -> pre_trail (Fmt.to_string State.pp_trail_elt elt))
          |> Iter.to_list |> div_class "ats-trail");
        details ~short:(Fmt.sprintf "clauses (%d)" (List.length cs))
          ~a:[title_f "@[<v>%a@]@." (Fmt.Dump.list Clause.pp) cs]
          (List.map (fun c -> pre_f "%a" Clause.pp c) cs |> div_class "ats-clauses");
      ]
  end)

module CDCL = Make_calculus(struct
    module A = Ats.ATS.Make(Ats.CDCL.A)
    open Ats.CDCL
    open Calculus_msg

    let kinds = [Ats_examples.K_cnf]
    let name = "cdcl"
    let view (st:State.t) : Calculus_msg.t Vdom.vdom =
      let open Vdom in
      let status, trail, cs = State.view st in
      div_class "ats-state" [
        div_class "ats-status" [h_status "status: "; pre (Fmt.to_string State.pp_status status)];
        details ~short:(Fmt.sprintf "trail (%d elts)" (Trail.length trail))
          ~a:[title_f "@[<v>%a@]" Trail.pp trail]
          (Trail.to_iter trail
          |> Iter.map
            (fun elt -> pre_trail (Fmt.to_string Trail.pp_trail_elt elt))
          |> Iter.to_list |> div_class "ats-trail");
        details ~short:(Fmt.sprintf "clauses (%d)" (List.length cs))
          ~a:[title_f "@[<v>%a@]@." (Fmt.Dump.list Clause.pp) cs]
          (List.map (fun c -> pre_f "%a" Clause.pp c) cs |> div_class "ats-clauses");
      ]
  end)

module MCSAT = Make_calculus(struct
    module A = Ats.ATS.Make(Ats.MCSAT.A)
    open Ats.MCSAT
    open Calculus_msg

    let kinds = [Ats_examples.K_smt]
    let name = "mcsat"
    let view (st:State.t) : Calculus_msg.t Vdom.vdom =
      let open Vdom in
      let status, cs, trail, env = State.view st in
      let a_status = match status with
        | Sat -> [color "green"; style "bold" "true"]
        | Unsat -> [color "red"; style "bold" "true"]
        | Conflict_uf _ | Conflict_bool _ -> [color "orange"]
        | Searching -> []
      in
      div_class "ats-state" [
        div_class "ats-status"
          [h_status ~a:a_status "status: "; pre (Fmt.to_string State.pp_status status)];
        details
          ~short:(Fmt.sprintf "trail (%d elts, level %d)"
                    (Trail.length trail) (Trail.level trail))
          ~a:[title_f "@[<v>%a@]@." Trail.pp trail]
          (Trail.to_iter trail
          |> Iter.map (fun elt -> pre_trail_f "%a" Trail.pp_trail_elt elt)
          |> Iter.to_list |> div_class "ats-trail"
        );
        details ~short:(Fmt.sprintf "clauses (%d)" (Clause.Set.cardinal cs))
          ~a:[title_f "@[<v>%a@]@." (Clause.Set.pp Clause.pp) cs]
          (Clause.Set.elements cs |> List.map (fun c -> pre_f "%a" Clause.pp c)
           |> div_class "ats-clauses"
        );
        details ~short:(Fmt.sprintf "env (%d)" (Env.length env))
          ~a:[title_f "%a@." Env.pp env]
          (Env.to_iter env
           |> Iter.map (fun c -> pre_f "%a" Env.pp_item c) |> Iter.to_list
           |> div_class "ats-clauses"
        );
      ]
  end)

module MCSAT_plus = Make_calculus(struct
    module A = Ats.ATS.Make(Ats.MCSAT_plus.A)
    open Ats.MCSAT_plus
    open Calculus_msg

    let kinds = [Ats_examples.K_smt]
    let name = "mcsat+"
    let view (st:State.t) : Calculus_msg.t Vdom.vdom =
      let open Vdom in
      let status, cs, trail, env = State.view st in
      let a_status = match status with
        | Sat -> [color "green"; style "bold" "true"]
        | Unsat -> [color "red"; style "bold" "true"]
        | Conflict_uf _ | Conflict_bool _ -> [color "orange"]
        | Searching -> []
      in
      div_class "ats-state" [
        div_class "ats-status"
          [h_status ~a:a_status "status: "; pre (Fmt.to_string State.pp_status status)];
        details
          ~short:(Fmt.sprintf "trail (%d elts, level %d)"
                    (Trail.length trail) (Trail.level trail))
          ~a:[title_f "@[<v>%a@]@." Trail.pp trail]
          (Trail.to_iter trail
           |> Iter.map
             (fun ((k,_,_) as elt) ->
                pre_trail_f ~a:[title_f "%a" Trail.pp_kind k]
                 "%a" Trail.pp_trail_elt elt)
           |> Iter.to_list |> div_class "ats-trail"
        );
        details ~short:(Fmt.sprintf "clauses (%d)" (Clause.Set.cardinal cs))
          ~a:[title_f "@[<v>%a@]@." (Clause.Set.pp Clause.pp) cs]
          (Clause.Set.elements cs |> List.map (fun c -> pre_f "%a" Clause.pp c)
           |> div_class "ats-clauses"
        );
        details ~short:(Fmt.sprintf "env (%d)" (Env.length env))
          ~a:[title_f "%a@." Env.pp env]
          (Env.to_iter env
           |> Iter.map (fun c -> pre_f "%a" Env.pp_item c) |> Iter.to_list
           |> div_class "ats-clauses"
        );
      ]
  end)

module MCSUP = Make_calculus(struct
    module A = Ats.ATS.Make(Ats.MCSUP.A)
    open Ats.MCSUP
    open Calculus_msg

    let kinds = [Ats_examples.K_smt]
    let name = "mcsup"
    let view (st:State.t) : Calculus_msg.t Vdom.vdom =
      let open Vdom in
      let status, cs, trail, env = State.view st in
      let prec = Trail.prec trail in
      let a_status = match status with
        | Sat -> [color "green"; style "bold" "true"]
        | Unsat -> [color "red"; style "bold" "true"]
        | Conflict_uf _ | Conflict_bool _ -> [color "orange"]
        | Searching -> []
      in
      div_class "ats-state" [
        div_class "ats-status"
          [h_status ~a:a_status "status: "; pre (Fmt.to_string State.pp_status status)];
        details
          ~short:(Fmt.sprintf "trail (%d elts, level %d)"
                    (Trail.length trail) (Trail.level trail))
          ~a:[title_f "@[<v>%a@]@." Trail.pp trail]
          (Trail.to_iter trail
           |> Iter.map
             (fun ((k,_,_) as elt) ->
                pre_trail_f ~a:[title_f "%a" Trail.pp_kind k]
                 "%a" Trail.pp_trail_elt elt)
           |> Iter.to_list |> div_class "ats-trail"
        );
        details ~short:(Fmt.sprintf "clauses (%d)" (Clause.Set.cardinal cs))
          ~a:[title_f "@[<v>%a@]@." (Clause.Set.pp Clause.pp) cs]
          (Clause.Set.elements cs |> List.map (fun c -> pre_f "%a" Clause.pp c)
           |> div_class "ats-clauses"
        );
        details ~short:(Fmt.sprintf "precedence (%d)" (Precedence.length prec))
          ~a:[title_f "%a@." Precedence.pp prec]
          (pre_f "@[<hv>%a@]" Precedence.pp prec);
        details ~short:(Fmt.sprintf "env (%d)" (Env.length env))
          ~a:[title_f "%a@." Env.pp env]
          (Env.to_iter env
           |> Iter.map (fun c -> pre_f "%a" Env.pp_item c) |> Iter.to_list
           |> div_class "ats-clauses"
        );
      ]
  end)

module App = struct
  open Vdom

  type msg =
    | M_none
    | M_use_calculus of string
    | M_set_parse of string
    | M_parse
    | M_set_cur of string * Ats_examples.kind * string
    | M_set_auto of string
    | M_calculus of Calculus_msg.t
    | M_and_then of msg list

  type logic_model =
    | LM : {
        app: (module APP_CALCULUS with type model = 'm);
        model: 'm;
      } -> logic_model
      
  type model = {
    error: string option;
    parse: string;
    cur_file: (string * Ats_examples.kind * string) option; (* [name, kind, content] *)
    auto: int;
    lm: logic_model;
  }

  let all_ : _ list =
    List.map
      (fun (module M:APP_CALCULUS) -> M.name, LM {app=(module M); model=M.init})
      [ (module DPLL);
        (module CDCL);
        (module MCSAT);
        (module MCSAT_plus);
        (module MCSUP);
      ]

  let init : model =
    { error=None; parse=""; auto=100; lm=List.assoc "mcsup" all_;
      cur_file=None; }

  let rec update (m:model) (msg:msg) : model =
    match msg, m with
    | M_none, _ -> m
    | M_use_calculus s, _ ->
      begin match List.assoc s all_, m.cur_file with
        | LM {app=(module App);_} as f, Some (pb, k_pb, s) when List.mem k_pb App.kinds ->
          (* use [f], then reload problem's content *)
          let reload =
            M_and_then [M_set_parse s; M_parse; M_set_cur (pb,k_pb,s)]
          in
          update {m with error=None; lm=f; parse=""} reload
        | f, _ ->
          (* incompatible/absent cur file, just remove *)
          {m with error=None; lm=f; cur_file=None; parse=""}
        | exception Not_found ->
          {m with error=Some (Printf.sprintf "unknown system %s" s)}
      end
    | M_set_parse s, _ -> {m with parse=s}
    | M_set_auto s, _ ->
      if String.trim s = "" then {m with auto=0}
      else (
        try {m with auto=int_of_string s}
        with _ -> {m with error=Some "auto should be an integer"}
      )
    | M_parse, {parse=s; lm; _} ->
      let lm' = match lm with
        | LM {app=(module App) as app; _} ->
          App.parse s |> CCResult.map (fun m -> LM {app; model=m})
      in
      begin match lm' with
        | Ok lm' -> {m with error=None; cur_file=None; lm=lm'; parse="";}
        | Error msg ->
          {m with error=Some msg; cur_file=None;}
      end
    | M_calculus msg, {lm=LM {app=(module App) as app; model};_} ->
      begin match App.update model msg with
        | Ok lm -> {m with error=None; lm=LM {app; model=lm}}
        | Error msg -> {m with error=Some msg}
      end
    | M_set_cur (file,k,content), _ -> {m with cur_file=Some (file,k,content)}
    | M_and_then l, _ -> List.fold_left update m l

  let view_ (m:model) =
    let {error; parse; lm=LM {app=(module App);_} as lm; cur_file; auto} = m in
    let v_error = match error with
      | None -> []
      | Some s -> [div ~a:[color "red"] [pre s]]
    and v_load = [ 
      div_class "ats-content"
        [div_class "ats-buttons" @@
         List.map
           (fun (s,_) -> button ~cls:"ats-button" ("use " ^ s) (M_use_calculus s)) all_];
    ]
    and v_load_parse_example = [
      CCList.filter_map
        (fun (k,name,s) ->
           if List.mem k App.kinds then (
             let b =
               button_f ~cls:"ats-button ats-button--example" ~a:[title s]
                 (M_and_then [M_set_parse s; M_parse; M_set_cur (name,k,s)]) "load %S" name in
             Some b
           ) else None)
        Ats_examples.all
      |> div_class "ats-parse-examples"
    ]
    and v_parse =
      div_class "ats-setting" [
        button ~cls:"ats-button ats-button--setup" "parse" M_parse;
        input [] ~a:[
          type_ "text"; value parse; id "set-parse"; str_prop "autocomplete" "on";
          on_key_enter ~default:M_none M_parse;
          oninput (fun s -> M_set_parse s)];
      ]
    and v_auto =
      let msg_auto = M_calculus (Calculus_msg.M_auto auto) in
      div_class "ats-setting" [
        button ~cls:"ats-button ats-button--setup" ~a:[title help_auto]
          "auto" msg_auto;
        input []
          ~a:[type_ "number"; str_prop "autocomplete" "on"; id "auto";
              value (if auto=0 then "" else string_of_int auto);
              on_key_enter ~default:M_none msg_auto;
              oninput (fun s -> M_set_auto s)];
    ]
    and v_lm = match lm with
      | LM {app=(module App); model} ->
        [App.view model |> map (fun x -> M_calculus x)]
    and v_cur = match cur_file with
      | None -> []
      | Some (f,_,_) -> [div_class "ats-cur" [text_f "[current: %S]" f]]
    in
    let v_settings = [
      section "ats-setup" [v_parse; v_auto]
    ] in
    div_class "ats-container" @@ List.flatten [
      v_error; v_load; v_load_parse_example; v_cur;
      v_settings; [section "ats-main" v_lm];
    ]

  let view m = Vdom.memo ~key:"main" view_ m

  let app = Vdom.simple_app ~init ~update ~view ()
end

open Js_browser

let run () = Vdom_blit.run App.app |> Vdom_blit.dom |> Element.append_child (Document.body document)
let () = Window.set_onload window run
