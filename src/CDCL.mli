(** {1 CDCL transition system} *)
open Util

module Lit : sig
  type t = int
  val compare : t -> t -> int
  val abs : t -> t
  val pp : t  Fmt.printer
  val parse : t P.t

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
end

module Clause : sig
  type t
  val of_list : Lit.t list -> t
  val pp : t  Fmt.printer
  val parse : t P.t
end

module State : sig
  type t

  val empty : t
  val pp : t Fmt.printer
  val parse : t P.t
end

module A : ATS.BASIC with module State = State

val ats : ATS.t


