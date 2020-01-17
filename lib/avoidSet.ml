(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type Set =
  sig
    type elt
    type t

    val empty : t
    val add   : elt -> t -> t
    val singleton : elt -> t
    val union : t -> t -> t
    val mem   : elt -> t -> bool
  end

module type S =
  sig
    type elt
    type set
    type t
    val empty : t
    val singleton : elt -> t
    val of_pred : (elt -> bool) -> t
    val of_set : set -> t
    val add : elt -> t -> t
    val union : t -> t -> t
    val mem : elt -> t -> bool
  end

module Make(S : Set) =
  struct
    type elt = S.elt
    type set = S.t

    type t =
      {
        pred : elt -> bool;
        set  : S.t;
      }

    let of_pred p =
      {
        pred = p;
        set  = S.empty
      }

    let of_set s =
      {
        pred = (fun _ -> false);
        set  = s
      }

    let singleton id =
      {
        pred = (fun _ -> false);
        set  = S.singleton id
      }


    let union {pred=p1; set = s1}
          {pred=p2; set = s2} =
      {pred = (fun id -> p1 id || p2 id);
       set  = S.union s1 s2
      }


    let add e {pred ; set} =
      {
        pred = pred;
        set  = S.add e set
      }

    let empty = {pred = (fun _ -> false) ; set = S.empty}


    let mem id {pred ; set} =
      pred id || S.mem id set

end
