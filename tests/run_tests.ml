module A = Alcotest

let suite = [
  Test_dpll.suite;
]

let () =
  Alcotest.run "ats" suite
