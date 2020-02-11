module type ARG = sig
  type t
  val equal : t -> t -> bool
  val hash : t -> int
  val set_id : t -> int -> unit
end

module Make(A : ARG): sig
  type t
  val create : ?size:int -> unit -> t
  val hashcons : t -> A.t -> A.t
  val to_iter : t -> A.t Iter.t
end = struct
  module W = Weak.Make(A)

  type t = {
    tbl: W.t;
    mutable n: int;
  }

  let create ?(size=1_024) () = {tbl=W.create size; n=0}

  (* hashcons terms *)
  let hashcons st t =
    let t' = W.merge st.tbl t in
    if t == t' then (
      A.set_id t' st.n;
      st.n <- 1 + st.n;
    );
    t'

  let to_iter st yield = W.iter yield st.tbl
end
