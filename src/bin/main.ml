open Util
module ATS = ATS

let ats_l : ATS.t list = [
  DPLL.ats;
  CDCL.ats;
  MCSAT.ats;
]

let default_ats = CDCL.ats

module Make_cmd(A: ATS.S) = struct
  type t =
    | Quit
    | Auto of int
    | Next of int
    | Show
    | Help of string option
    | Pick of int
    | Init of A.State.t

  let all_ = [
    "quit", " quits";
    "show", " show current state";
    "init", " <st> parse st and sets current state to it";
    "next", " <n>? transition to next state (n times if provided)";
    "auto", " <n?> run next|pick in a loop, automatically (n times if provided)";
    "pick", " <i> pick state i in list of choices";
    "help", " show help";
  ]

  (* command parser *)
  let parse : t P.t =
    let open P in
    let int_or default = skip_white *> ((P.try_ U.int) <|> return default) in
    skip_white *> parsing "command" (
      (try_ (string "quit") *> return Quit)
      <|> (try_ (string "show") *> return Show)
      <|> (try_ (string "auto") *> (int_or max_int >|= fun i -> Auto i))
      <|> (try_ (string "init") *> skip_white *> (A.State.parse >|= fun st -> Init st))
      <|> (try_ (string "pick") *> skip_white *> (U.int >|= fun i -> Pick i))
      <|> (try_ (string "next") *> (int_or 1 >|= fun i -> Next i))
      <|> (try_ (string "help") *> skip_white *>
           ((P.try_ U.word >|= CCOpt.return) <|> return None) >|= fun what ->
           Help what)
      <|> P.fail "invalid command"
    ) <* skip_white

  let hints (s:string) : _ option =
    match List.assoc (String.trim s) all_ with
    | h -> Some (h, LNoise.Blue, false)
    | exception _ -> None

  (* provide basic completions *)
  let complete (s:string) : string list =
    CCList.filter_map
      (fun (cmd,_) ->
         if CCString.prefix ~pre:s cmd then Some cmd else None)
      all_
end

(* multi-line input if there are more "(" than ")" so far *)
let lnoise_input prompt : string option =
  let buf = Buffer.create 32 in
  let depth = ref 0 in (* balance "(" and ")" *)
  let first = ref true in
  let rec loop () =
    let p = if !first then prompt else String.make (String.length prompt) ' ' in
    first := false;
    match LNoise.linenoise p with
    | None when Buffer.length buf=0 -> None
    | None -> Some (Buffer.contents buf)
    | Some s ->
      String.iter (function '(' -> incr depth | ')' -> decr depth | _ -> ()) s;
      Buffer.add_string buf s;
      if !depth <= 0 then Some (Buffer.contents buf) else loop()
  in
  loop()

let repl ?(ats=default_ats) () =
  let (module A) = ats in
  let module Cmd = Make_cmd(A) in
  let module R = Run.Make(A) in
  (* current state *)
  let cur_st_ = ref A.State.empty in
  let choices_ : (A.State.t * string) list option ref = ref None in
  let done_ = ref false in
  LNoise.set_multiline false;
  (* completion of commands *)
  LNoise.set_completion_callback
    (fun s compl ->
       Cmd.complete s |> List.iter (LNoise.add_completion compl));
  (* show help for commands *)
  LNoise.set_hints_callback Cmd.hints;
  (* print active list of choices *)
  let pp_choices l =
    Fmt.printf "@[<v2>@{<yellow>choices@}:@ %a@]@."
      (Util.pp_list
         Fmt.(within "(" ")" @@ hbox @@ pair ~sep:(return ": ") int
                (pair ~sep:(return " by@ ") A.State.pp string_quoted)))
      (CCList.mapi CCPair.make l);
  in
  let rec pp_transition out tr =
    let open R.Transition in
    match tr.expl with
    | Choice (i,expl) ->
      Fmt.fprintf out "@[<2>@{<yellow>choice@}[%d] %S to@ %a@]" i expl A.State.pp tr.final;
    | Deterministic expl ->
      Fmt.fprintf out "@[<2>@{<green>deterministic transition@} %S to@ %a@]"
        expl A.State.pp tr.final;
    | Multi_deterministic l ->
      Fmt.fprintf out "@[<2>@{<green>multiple-steps@}[%d] to@ %a@ @[<hv2>:steps@ %a@]@]"
        (List.length l) A.State.pp tr.final pp_transitions l;
  and pp_transitions out l =
    Fmt.fprintf out "@[<v>%a@]" (pp_list pp_transition) l
  in
  let pp_trace tr : unit =
    let open R.Trace in
    match tr.R.Trace.status with
    | Stopped ->
      Fmt.printf "@[<v>%a@,@[<2>@{<Green>done@} last state:@ %a@]@]@."
        pp_transitions tr.transitions A.State.pp tr.final;
    | Active ->
      begin match tr.transitions with
        | [] -> Fmt.printf "%a@." A.State.pp !cur_st_;
        | _ -> Fmt.printf "@[<v>%a@]@." pp_transitions tr.transitions;
      end;
    | Error msg ->
      Fmt.printf "@[<v>%a@,@{<Red>error@}: %s@]@." pp_transitions tr.transitions msg;
  in
  let rec loop () =
    match lnoise_input "> " |> CCOpt.map String.trim with
    | exception Sys.Break -> loop()
    | None -> () (* exit *)
    | Some "" -> loop()
    | Some s ->
      match P.parse_string Cmd.parse s with
      | Error msg ->
        Fmt.printf "@{<Red>error@}: invalid command: %s@." msg;
        loop()
      | Ok Cmd.Quit -> () (* exit *)
      | Ok cmd ->
        LNoise.history_add s |> ignore; (* save cmd *)
        process_cmd cmd;
        loop();
  and process_cmd = function
    | Cmd.Quit -> assert false
    | Cmd.Help None ->
      Format.printf "available commands: [@[%a@]]@."
        (pp_list Fmt.string)
        (List.map fst Cmd.all_);
    | Cmd.Help (Some cmd) ->
      if List.mem_assoc cmd Cmd.all_ then (
        let h = List.assoc cmd Cmd.all_ in
        Format.printf "%s@." h
      ) else (
        Format.printf "@{<Red>error@}: unknown command %S" cmd
      )
    | Cmd.Show ->
      Fmt.printf "@[<2>state:@ %a@]@." A.State.pp !cur_st_;
      CCOpt.iter pp_choices !choices_;
    | Cmd.Auto n ->
      let trace, choices = R.run (R.Tactic.Auto n) !cur_st_ in
      pp_trace trace;
      cur_st_ := trace.R.Trace.final;
      done_ := R.Trace.is_done trace;
      choices_ := choices;
    | Cmd.Next _ when !done_ ->
      Fmt.printf "@{<Red>error@}: already in final state@.";
    | Cmd.Next n when n <= 0 ->
      Fmt.printf "@{<Red>error@}: need positive integer, not %d@." n;
    | Cmd.Next n ->
      let trace, choices = R.run (R.Tactic.Next n) !cur_st_ in
      pp_trace trace;
      cur_st_ := trace.R.Trace.final;
      done_ := R.Trace.is_done trace;
      choices_ := choices;
      CCOpt.iter pp_choices !choices_;
    | Cmd.Init st ->
      done_ := false;
      choices_ := None;
      cur_st_ := st
    | Cmd.Pick i ->
      begin match !choices_, CCOpt.flat_map (fun l -> List.nth_opt l i) !choices_ with
        | _, Some (c,expl) ->
          Fmt.printf "@[<2>@{<yellow>picked@} %d: next state by %S@ %a@]@."
            i expl A.State.pp c;
          choices_ := None;
          cur_st_ := c;
        | None, _ ->
          Fmt.printf "@{<Red>error@}: no active choice list@."
        | Some l, None ->
          Fmt.printf "@{<Red>error@}: invalid choice %d, must be in (0..%d)@."
            i (List.length l)
      end
  in
  loop ()

let () =
  let ats_ = ref default_ats in
  let color_ = ref true in
  let find_ats_ s =
    match List.find (fun a -> ATS.name a = s) ats_l with
    | a -> ats_ := a
    | exception _ -> Util.errorf "unknown ATS: %S" s
  in
  let opts = [
    ("-s", Arg.Symbol (List.map ATS.name ats_l, find_ats_),
     Printf.sprintf " choose transition system (default %s)" (ATS.name default_ats));
    ("-nc", Arg.Clear color_, " disable colors");
  ] |> Arg.align
  in
  Arg.parse opts (fun _ -> ()) "usage: ats [option*]";
  Fmt.set_color_default !color_;
  Printf.printf "picked ats %s\n%!" (ATS.name !ats_);
  LNoise.history_load ~filename:".ats-history" |> ignore;
  LNoise.history_set ~max_length:1000 |> ignore;
  repl ~ats:!ats_ ();
  LNoise.history_save ~filename:".ats-history" |> ignore;
  ()
