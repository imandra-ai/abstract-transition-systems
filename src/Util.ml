module Fmt = CCFormat
module P = CCParse

let pp_list ?(sep="") pp out l=
  Fmt.(list ~sep:(fun oc () -> fprintf oc "%s@ " sep) pp) out l

exception Error of string

let error e = raise (Error e)
let errorf f = Fmt.kasprintf error f
