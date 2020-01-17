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


module Make(S : Set) : (S with type elt = S.elt and type set = S.t)
