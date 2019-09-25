module A = Alcotest
module D = Ats.DPLL

type exp = E_sat | E_unsat

let pbs = [
  {|((-1 2) (1 2) (-3 2) (3 1) (-2 -1 -3) (2 3))|}, Some E_sat;
  {|((-1 2) (1 2) (-3 2) (3 1) (-2 -1 -3) (-2 3) (-3 1))|}, Some E_unsat;
  {|((-1 2) (1 2) (-3 2) (3 1) (-2 -1 -3) (-2 3) (-3 2))|}, Some E_sat;
  {|((1 2)(-1 2))|}, Some E_sat;
  {|(1|}, None;
]

let test_parse (pb,res) : unit A.test_case =
  let must_parse = CCOpt.is_some res in
  A.test_case (Printf.sprintf "pb_must_parse:%b" must_parse) `Quick @@ fun () ->
  match Ats.Sexp_parser.parse_string_str D.State.parse pb with
  | Ok _ ->
    if not must_parse then A.failf "%S should not parse" pb
  | Error msg -> if must_parse then A.failf "%S failed to parse: %s" pb msg

let suite : unit A.test =
  let tests = [
    List.map test_parse pbs;
  ] |> CCList.flatten in
  "dpll", tests
