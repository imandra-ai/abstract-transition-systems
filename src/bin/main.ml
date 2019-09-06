open Util
module ATS = ATS

let ats_l : ATS.t list = [
  DPLL.ats;
]

module Cmd(A: ATS.S) = struct
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

let repl ?(ats=DPLL.ats) () =
  let (module A) = ats in
  let module Cmd = Cmd(A) in
  (* current state *)
  let cur_st_ = ref A.State.empty in
  let choices_ : (A.State.t * string) list ref = ref [] in
  let done_ = ref false in
  LNoise.set_multiline false;
  (* completion of commands *)
  LNoise.set_completion_callback
    (fun s compl ->
       Cmd.complete s |> List.iter (LNoise.add_completion compl));
  (* show help for commands *)
  LNoise.set_hints_callback Cmd.hints;
  (* print active list of choices *)
  let pp_choices l=
    Fmt.printf "@[<v2>@{<yellow>choices@}:@ %a@]@."
      (Util.pp_list
         Fmt.(within "(" ")" @@ hbox @@ pair ~sep:(return ": ") int
                (pair ~sep:(return " by@ ") A.State.pp string_quoted)))
      (CCList.mapi CCPair.make l);
  in
  let call_next_once_ ~on_choice =
    match A.next !cur_st_ with
    | ATS.Done (st', expl) ->
      Fmt.printf "@[<2>@{<Green>done@} by %S, last state:@ %a@]@." expl A.State.pp st';
      cur_st_ := st';
      done_ := true
    | ATS.Error msg ->
      Fmt.printf "@{<Red>error@}: %s@." msg;
    | ATS.One (st', expl) | ATS.Choice [(st', expl)] ->
      Fmt.printf "@[<2>@{<green>deterministic transition@} %S to@ %a@]@."
        expl A.State.pp st';
      cur_st_ := st';
    | ATS.Choice [] -> assert false
    | ATS.Choice l ->
      on_choice l;
  in
  (* run [A.next] at most [i] times, but stop if it finishes or a choice
     must be made. *)
  let rec do_next i =
    if i<=0 then ()
    else if !done_ then ()
    else (
      call_next_once_ ~on_choice:(fun l -> choices_ := l; pp_choices l);
      if !choices_ = [] then do_next (i-1)
    );
  in
  let rec do_auto i =
    let auto_choice = function
      | [] -> assert false
      | (st',expl) :: _ ->
        Fmt.printf "@[<2>@{<yellow>auto-choice@} %S to@ %a@]@." expl A.State.pp st';
        choices_ := [];
        cur_st_ := st';
    in
    match !choices_ with
    | _ when i<0 -> ()
    | _ when !done_ -> ()
    | [] ->
      (* do one step of [next], with automatic choice if needed *)
      call_next_once_ ~on_choice:auto_choice;
      do_auto (i-1)
    | l ->
      auto_choice l;
      do_auto (i-1);
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
      if !choices_ <> [] then pp_choices !choices_
    | Cmd.Auto n ->
      do_auto n
    | Cmd.Next _ when !done_ ->
      Fmt.printf "@{<Red>error@}: already in final state@.";
    | Cmd.Next n when n <= 0 ->
      Fmt.printf "@{<Red>error@}: need positive integer, not %d@." n;
    | Cmd.Next n ->
      do_next n
    | Cmd.Init st ->
      done_ := false;
      choices_ := [];
      cur_st_ := st
    | Cmd.Pick i ->
      begin match List.nth !choices_ i with
        | (c,expl) ->
          Fmt.printf "@[<2>@{<yellow>picked@} %d: next state by %S@ %a@]@."
            i expl A.State.pp c;
          choices_ := [];
          cur_st_ := c;
        | exception _ ->
          Fmt.printf "@{<Red>error@}: invalid choice %d, must be in (0..%d)@."
            i (List.length !choices_)
      end
  in
  loop ()

let () =
  let ats_ = ref DPLL.ats in
  let color_ = ref true in
  let find_ats_ s =
    match List.find (fun a -> ATS.name a = s) ats_l with
    | a -> ats_ := a
    | exception _ -> Util.errorf "unknown ATS: %S" s
  in
  let opts = [
    "-s", Arg.Symbol (List.map ATS.name ats_l, find_ats_), " choose transition system";
    "-nc", Arg.Clear color_, " disable colors";
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
