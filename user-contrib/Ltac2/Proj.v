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

Ltac2 Type t := projection.
(** Type of primitive projections. This includes the unfolding boolean. *)

Ltac2 @ external equal : t -> t -> bool := "rocq-runtime.plugins.ltac2" "projection_equal".
(** Projections obtained through module aliases or Include are not
    considered equal by this function. The unfolding boolean is not ignored. *)

Ltac2 @ external ind : t -> inductive := "rocq-runtime.plugins.ltac2" "projection_ind".
(** Get the inductive to which the projectin belongs. *)

Ltac2 @ external index : t -> int := "rocq-runtime.plugins.ltac2" "projection_index".
(** The index of the projection indicates which field it projects. *)

Ltac2 @ external unfolded : t -> bool := "rocq-runtime.plugins.ltac2" "projection_unfolded".
(** Get the unfolding boolean. *)

Ltac2 @ external set_unfolded : t -> bool -> t
  := "rocq-runtime.plugins.ltac2" "projection_set_unfolded".
(** Set the unfolding boolean. *)

Ltac2 @ external of_constant : constant -> t option
  := "rocq-runtime.plugins.ltac2" "projection_of_constant".
(** Get the primitive projection associated to the constant.
    The returned projection is folded.
    Returns [None] when the constant is not associated to a primitive projection. *)

Ltac2 @ external to_constant : t -> constant option
  := "rocq-runtime.plugins.ltac2" "projection_to_constant".
(** Get the constant associated to the primitive projection.
    Currently always returns [Some] but this may change in the future. *)
