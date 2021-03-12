(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Ltac2 Require Import Init.

Ltac2 Type t := inductive.

Ltac2 @ external equal : t -> t -> bool := "ltac2" "ind_equal".
(** Equality test. *)

Ltac2 Type data.
(** Type of data representing inductive blocks. *)

Ltac2 @ external data : t -> data := "ltac2" "ind_data".
(** Get the mutual blocks corresponding to an inductive type in the current
    environment. Panics if there is no such inductive. *)

Ltac2 @ external repr : data -> t := "ltac2" "ind_repr".
(** Returns the inductive corresponding to the block. Inverse of [data]. *)

Ltac2 @ external index : t -> int := "ltac2" "ind_index".
(** Returns the index of the inductive type inside its mutual block. Guaranteed
    to range between [0] and [nblocks data - 1] where [data] was retrieved
    using the above function. *)

Ltac2 @ external nblocks : data -> int := "ltac2" "ind_nblocks".
(** Returns the number of inductive types appearing in a mutual block. *)

Ltac2 @ external nconstructors : data -> int := "ltac2" "ind_nconstructors".
(** Returns the number of constructors appearing in the current block. *)

Ltac2 @ external get_block : data -> int -> data := "ltac2" "ind_get_block".
(** Returns the block corresponding to the nth inductive type. Index must range
    between [0] and [nblocks data - 1], otherwise the function panics. *)

Ltac2 @ external get_constructor : data -> int -> constructor := "ltac2" "ind_get_constructor".
(** Returns the nth constructor of the inductive type. Index must range between
    [0] and [nconstructors data - 1], otherwise the function panics. *)
