module Fmt = CCFormat
module P = Sexp_parser
module Option = CCOpt

let quiet_ = ref false

let pp_list ?(sep="") pp out l=
  Fmt.(list ~sep:(fun oc () -> fprintf oc "%s@ " sep) pp) out l

let pp_iter ?(sep="") pp out l=
  Fmt.(iter ~sep:(fun oc () -> fprintf oc "%s@ " sep) pp) out l

exception Error of string

let error e = raise (Error e)
let errorf f = Fmt.kasprintf error f

module Str_tbl = CCHashtbl.Make(CCString)
module Str_map = CCMap.Make(CCString)
