open Util

module L = CCList

module type S = sig
  module A : ATS.S

  module Cmd0 : sig
    type t =
      | Quit
      | Auto of int
      | Next of int
      | Show
      | Help of string option
      | Pick of int
      | Init of A.State.t
  end

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
    type t = {
      init: A.State.t;
      final: (A.State.t, string) result;
      stopped: bool;
      transitions: Transition.t L.t;
    }

    val trivial : A.State.t -> t
    val append : t -> t -> t
    val transitions : t -> Transition.t Iter.t
    val pp : t Fmt.printer

    module Infix : sig
      val (<+>) : t -> t -> t
    end
    include module type of Infix
  end

  val run : Cmd0.t -> A.State.t -> Trace.t
end
