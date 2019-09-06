open Util

module Lit = struct
  type t = int
  let pp = Fmt.int
  let parse = P.(skip_white *> U.int)
end

module Clause = struct
  type t = Lit.t list
  let pp out c = Fmt.fprintf out "(@[%a@])" (pp_list Lit.pp) c

  let parse : t P.t =
    let open P in
    (skip_white *> char '(' *> many (try_ Lit.parse)) <* try_ (skip_white <* char ')')
end

module State = struct
  type t = {
    cs: Clause.t list;
    trail: Lit.t list;
  }

  let make cs trail : t = {cs;trail}
  let empty = make [] []

  let pp out (self:t) =
    let {cs; trail} = self in
    Fmt.fprintf out "(@[st @[:cs@ (@[%a@])@]@ @[:trail@ (@[%a@])@]@])"
      (pp_list Clause.pp) cs (pp_list Lit.pp) trail

  let parse : t P.t =
    let open P in
    (skip_white *> char '(' *> many Clause.parse <* skip_white <* char ')')
    >|= fun cs -> make cs []
end

module A = struct
  let name = "dpll"
  module State = State
  let next _ = assert false
end

let ats : ATS.t = (module A)
