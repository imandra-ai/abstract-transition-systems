open Util
module ATS = ATS

let ats_l : ATS.t list = [
  DPLL.ats;
]

let repl ?(ats=DPLL.ats) () =
  let (module A) = ats in
  (* current state *)
  let cur_st_ = ref A.State.empty in
  let done_ = ref false in
  LNoise.set_multiline false;
  let all_cmds_ = [
    "quit", " quits";
    "show", " show current state";
    "init", " <st> parse st and sets current state to it";
    "step", " transition to next state";
    "help", " show help";
  ] in
  (* completion of commands *)
  LNoise.set_completion_callback
    (fun s compl ->
       List.iter
         (fun (cmd,_) ->
            if CCString.prefix ~pre:s cmd then LNoise.add_completion compl cmd)
         all_cmds_);
  (* show help for commands *)
  LNoise.set_hints_callback (fun s ->
      match List.assoc (String.trim s) all_cmds_ with
      | h -> Some (h, LNoise.Blue, false)
      | exception _ -> None);
  let rec loop () =
    match LNoise.linenoise "> " with
    | None -> () (* exit *)
    | Some s ->
      let s = String.trim s in
      match s with
      | "" -> loop ()
      | "quit" -> ()
      | "help" ->
        Format.printf "available commands: [@[%a@]]@."
          (pp_list Fmt.string)
          (List.map fst all_cmds_);
        loop()
      | "show" ->
        LNoise.history_add s |> ignore;
        Fmt.printf "@[<2>state:@ %a@]@." A.State.pp !cur_st_;
        loop()
      | "next" when !done_ ->
        Fmt.printf "@{<Red>error@}: already in final state@.";
        loop()
      | "next" ->
        LNoise.history_add s |> ignore;
        begin match A.next !cur_st_ with
          | ATS.Done st' ->
            Fmt.printf "@[<2>done, last state:@ %a@]@." A.State.pp st';
            cur_st_ := st'; done_ := true
          | ATS.Error msg ->
            Fmt.printf "@{<Red>error@}: %s@." msg;
          | ATS.One st' | ATS.Choice [st'] ->
            Fmt.printf "@[<2>deterministic transition to@ %a@]@." A.State.pp st';
            cur_st_ := st';
          | ATS.Choice [] -> assert false
          | ATS.Choice _l ->
            Fmt.printf "TODO: multiple choices@.'" (* TODO *)
        end;
        loop()
      | _ ->
        begin match CCString.Split.left ~by:" " s with
          | Some ("help", cmd) ->
            if List.mem_assoc cmd all_cmds_ then (
              LNoise.history_add s |> ignore;
              let h = List.assoc cmd all_cmds_ in
              Format.printf "%s@." h
            ) else (
              Format.printf "error: unknown command %S" cmd
            )
        | Some ("init", st) ->
          (* set initial state *)
          begin match P.parse_string A.State.parse st with
            | Error e ->
              Fmt.printf "error: invalid state: %s@." e
            | Ok st ->
              LNoise.history_add s |> ignore;
              done_ := false;
              cur_st_ := st
          end
        | _ ->
          Fmt.printf "invalid command@.";
        end;
        loop ()
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
