(* generate examples from files in ../../examples  *)


let () =
  let files =
    CCIO.File.walk_l "../../examples"
    |> CCList.filter_map (function (`File,f) -> Some f | _ -> None)
  in
  let buf = Buffer.create 256 in
  Printf.bprintf buf "let all = [\n";
  List.iter (fun f ->
      let content = CCIO.with_in f CCIO.read_all in
      let f = Filename.basename f in
      Printf.bprintf buf "%S, {|%s|};\n" f content)
    files;
  Printf.bprintf buf "];;\n";
  print_endline (Buffer.contents buf)
