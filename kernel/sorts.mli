(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {6 The sorts of CCI. } *)

type family = InProp | InSet | InType

type t =
  | Prop
  | Set
  | Type of Univ.Universe.t

val set  : t
val prop : t
val type1  : t

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

val is_set : t -> bool
val is_prop : t -> bool
val is_small : t -> bool
val family : t -> family

val hcons : t -> t

val family_equal : family -> family -> bool

module List : sig
  val mem : family -> family list -> bool
  val intersect : family list -> family list -> family list
end

val univ_of_sort : t -> Univ.Universe.t
val sort_of_univ : Univ.Universe.t -> t
