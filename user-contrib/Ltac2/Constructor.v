(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

Ltac2 Type t := constructor.

Ltac2 @ external equal : t -> t -> bool := "rocq-runtime.plugins.ltac2" "constructor_equal".
(** Constructors obtained through module aliases or Include are not
    considered equal by this function. *)

Ltac2 @ external inductive : t -> inductive := "rocq-runtime.plugins.ltac2" "constructor_inductive".
(** Returns the inductive to which the given constructor belongs. *)

Ltac2 @ external index : t -> int := "rocq-runtime.plugins.ltac2" "constructor_index".
(** Returns the index of the given constructor
    (such that [c] is [Ind.get_constructor (Ind.data (inductive c)) (index c)]). *)
