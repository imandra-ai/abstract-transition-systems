(* generate examples from files in ../../examples  *)

let prelude = {|
type kind = K_smt | K_cnf
let all = [
|};;

let () =
  let files =
    CCIO.File.walk_l "../../examples"
    |> CCList.filter_map (function (`File,f) -> Some f | _ -> None)
    |> List.sort String.compare
  in
  let buf = Buffer.create 256 in
  Buffer.add_string buf prelude;
  List.iter (fun f ->
      let content = CCIO.with_in f CCIO.read_all in
      let cat = Filename.basename @@ Filename.dirname f in
      let f = Filename.basename f in
      Printf.bprintf buf "K_%s, %S, {|%s|};\n" cat f content)
    files;
  Printf.bprintf buf "];;\n";
  print_endline (Buffer.contents buf)
