(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type ValueS =
sig
  type 'a t
end

(** Polymorphic maps over an extensible GADT tag type. *)

module type Tag = sig type _ tag = .. end

module Make (Tag:Tag) : sig
  open Tag

  module type OneTag = sig
    type a
    type _ tag += T : a tag
  end
  type 'a onetag = (module OneTag with type a = 'a)
  (** There is no equality function between [_ tag] values (other than
      [Stdlib.(=)]), and especially no equality function which shows
      that when the values are equal the type arguments are also
      equal.

      Instead we can use ['a onetag] to recognize ['b tag] values. *)

  val eq_onetag : 'a onetag -> 'b tag -> ('a,'b) CSig.eq option

  val make : unit -> 'a onetag

  val tag_of_onetag : 'a onetag -> 'a tag

  module type MapS = sig
    type t
    type _ value

    val empty : t

    val find : 'a tag -> t -> 'a value

    val add : 'a onetag -> 'a value -> t -> t

    val mem : 'a tag -> t -> bool

    val modify : 'a tag -> ('a value -> 'a value) -> t -> t

  end
  module Map(V:ValueS) : MapS with type 'a value := 'a V.t

end
