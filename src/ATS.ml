(** {1 Abstract transition system} *)

open Util

type 'a step =
  | Done of 'a (* final state *)
  | Error of string
  | One of 'a (* forced transition *)
  | Choice of 'a list

type ('a, 'b) rule = 'a  -> 'b step option

(** {2 Minimum implementation of an abstract transition system implementation} *)
module type BASIC = sig
  val name : string

  module State : sig
    type t
    val empty : t
    val pp : t Fmt.printer
    val parse : t P.t
  end

  (** A set of rules, by decreasing layer of priority. Each rule
      can fire, returning new states (with explanation for the transition),
      or return [None] *)
  val rules : (State.t, State.t * string) rule list list
end

(** An abstract transition system implementation *)
module type S = sig
  include BASIC

  val next : State.t -> (State.t * string) step
end

module Make(B : BASIC)
  : S with module State = B.State
= struct
  include B

  let merge_ s1 s2 =
    match s1, s2 with
    | Error _, _ -> s1
    | _, Error _ -> s2
    | Done _, _ -> s1
    | _, Done _ -> s2
    | One a, One b -> Choice [a;b]
    | One a, Choice l -> Choice (a::l)
    | Choice l, One a -> Choice (a::l)
    | Choice l1, Choice l2 -> Choice (List.rev_append l2 l1)

  let rec next_ st rss =
    match rss with
    | [] -> Error "no applicable transition"
    | rs :: rss' ->
      let steps = CCList.filter_map (fun r -> r st) rs in
      match steps with
      | [] -> next_ st rss'
      | [s] -> s
      | s1 :: steps' ->
        List.fold_left merge_ s1 steps'

  (* try all rules *)
  let next st = next_ st B.rules
end

type t = (module S)

let name (self:t) : string = let (module A) = self in A.name
