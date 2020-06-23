(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZifyClasses ZifyInst.
Declare ML Module "zify_plugin".

(** [zify_pre_hook] and [zify_post_hook] are there to be redefined. *)
Ltac zify_pre_hook := idtac.

Ltac zify_post_hook := idtac.

Ltac iter_specs := zify_iter_specs.

Ltac zify := intros;
             zify_pre_hook ;
             zify_elim_let ;
             zify_op ;
             (zify_iter_specs) ;
             zify_saturate ; zify_post_hook.
