open Util

module L = CCList

module type S = sig
  module A : ATS.S

  module Transition : sig
    type t = {
      init: A.State.t;
      final: A.State.t;
      expl: expl;
    }
    and expl =
      | Choice of int * string
      | Deterministic of string
      | Multi_deterministic of t list (* aggregate of deterministic transitions *)

    val pp : t Fmt.printer
  end

  module Trace : sig
    type status =
      | Active
      | Stopped
      | Error of string

    type t = {
      init: A.State.t;
      final: A.State.t;
      status: status;
      transitions: Transition.t L.t;
    }

    val trivial : A.State.t -> t
    val append : t -> t -> t
    val transitions : t -> Transition.t Iter.t
    val pp : t Fmt.printer
    val is_done : t -> bool (** not active *)

    module Infix : sig
      val (<+>) : t -> t -> t
    end
    include module type of Infix
  end

  module Tactic : sig
    type t =
      | Auto of int
      | Next of int (* only follow deterministic transitions and unique choices *)
    val pp : t Fmt.printer
  end

  type choice = (A.State.t * string) list

  val run : Tactic.t -> A.State.t -> Trace.t * choice option
end
