(** {1 Abstract transition system} *)

open Util

type 'a step =
  | Done
  | Error of string
  | Sub of 'a list

(** An abstract transition system implementation *)
module type S = sig
  val name : string

  module State : sig
    type t
    val empty : t
    val pp : t Fmt.printer
    val parse : t P.t
  end

  (* TODO: set of rules instead *)
  val next : State.t -> State.t step
end

type t = (module S)

let name (self:t) : string = let (module A) = self in A.name
