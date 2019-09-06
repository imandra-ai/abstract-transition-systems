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
    | Idle
  type t = private {
    cs: Clause.t list;
    trail: trail;
    status: status;
    _all_vars: Lit.Set.t lazy_t;
    _to_decide: Lit.Set.t lazy_t;
    _assign: bool Lit.Map.t lazy_t; (* assignment, from trail *)
  }

  val empty : t
  val make : Clause.t list -> trail -> status -> t
  val pp : t Fmt.printer
  val parse : t P.t
end

module A : ATS.S with module State = State

val ats : ATS.t


