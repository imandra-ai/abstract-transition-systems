(** {1 DPLL transition system} *)
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
  type t = Lit.t list
  val pp : t  Fmt.printer
  val parse : t P.t
end

module State : sig
  type trail_kind = Decision | Prop of Clause.t
  type trail_elt = trail_kind * Lit.t
  type trail = trail_elt list
  type status = private
    | Sat
    | Unsat
    | Conflict of Clause.t
    | Searching
  type t
  val view : t -> status * trail * Clause.t list

  val empty : t
  val make : Clause.t list -> trail -> status -> t
  val pp : t Fmt.printer
  val pp_status : status Fmt.printer
  val pp_trail_elt : trail_elt Fmt.printer
  val pp_trail : trail Fmt.printer
  val parse : t P.t
end

module A : ATS.BASIC with module State = State

val ats : ATS.t


