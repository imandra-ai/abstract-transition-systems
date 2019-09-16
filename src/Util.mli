module Fmt = CCFormat
module P = CCParse

val pp_list : ?sep:string -> 'a Fmt.printer -> 'a list Fmt.printer
val pp_iter : ?sep:string -> 'a Fmt.printer -> 'a Iter.t Fmt.printer

exception Error of string

val error : string -> 'a
val errorf : ('a, Format.formatter, unit, unit, unit, 'b) format6 -> 'a

module Str_tbl : CCHashtbl.S with type key = string
