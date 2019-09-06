(** {1 DPLL transition system} *)
open Util

module Lit : sig
  type t = int
  val pp : t  Fmt.printer
  val parse : t P.t
end

module Clause : sig
  type t = Lit.t list
  val pp : t  Fmt.printer
  val parse : t P.t
end

module State : sig
  type t = private {
    cs: Clause.t list;
    trail: Lit.t list;
  }

  val empty : t
  val make : Clause.t list -> Lit.t list -> t
  val pp : t Fmt.printer
  val parse : t P.t
end

module A : ATS.S with module State = State

val ats : ATS.t


