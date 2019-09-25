module Fmt = CCFormat
type sexp = CCSexp.t
type error

val string_of_error : error -> string
val pp_error : error Fmt.printer

type 'a t = sexp -> ('a,error) result

val fail : string -> _ t
val failf : ('a, Format.formatter, unit, 'v t) format4 -> 'a
val return : 'a -> 'a t
val int : int t
val bool : bool t
val float : float t
val string : string t
val list1 : 'a t -> 'a t
val list2 : 'a t -> 'b t -> ('a * 'b) t
val value : sexp t
val list_value : sexp list t
val list : 'a t -> 'a list t
val uncons : 'a t -> ('a -> 'b t) -> 'b t
val parsing: string -> 'a t -> 'a t
val fix : ('a t -> 'a t) -> 'a t
val match_ : atom:'a t -> list:'a t -> 'a t
val is_nil : bool t
val one_of : (string * 'a t) list -> 'a t

module Infix : sig
  val (>|=) : 'a t -> ('a -> 'b) -> 'b t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
end
include module type of Infix

val parse_string : 'a t -> string -> ('a, error) result
val parse_string_str : 'a t -> string -> ('a, string) result
val parse_file : 'a t -> string -> ('a, error) result
val parse_file_str : 'a t -> string -> ('a, string) result
