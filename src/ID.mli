(* This file is free software. See file "license" for more details. *)

(** {1 Unique Identifiers} *)

open Util

type t

val make : string -> t
val makef : ('a, Format.formatter, unit, t) format4 -> 'a
val copy : t -> t

val id : t -> int
val name : t -> string

val to_string : t -> string
val to_string_full : t -> string

val equal : t -> t -> bool
val hash : t -> int
val compare : t -> t -> int
val pp : t Fmt.printer
val pp_full : t Fmt.printer
val pp_name : t Fmt.printer

val _pp_full : bool ref

module Map : CCMap.S with type key = t
module Set : CCSet.S with type elt = t
module Tbl : CCHashtbl.S with type key = t
