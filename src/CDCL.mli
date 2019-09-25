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

module Trail : sig
  type kind = Decision | Prop of Clause.t
  type trail_elt = kind * Lit.t
  type t

  val pp_trail_elt : trail_elt Fmt.printer
  val to_iter : t -> trail_elt Iter.t
  val pp : t Fmt.printer
  val length : t -> int
end


module State : sig
  type status =
    | Sat
    | Unsat
    | Conflict of Clause.t
    | Backjump of Clause.t
    | Searching

  type t

  val empty : t
  val pp : t Fmt.printer
  val parse : t P.t
  val pp_status : status Fmt.printer

  val view : t -> status * Trail.t * Clause.t list
end

module A : ATS.BASIC with module State = State

val ats : ATS.t


