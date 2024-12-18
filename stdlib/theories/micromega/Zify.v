(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZifyClasses ZifyInst.
Declare ML Module "rocq-runtime.plugins.zify".

(** [zify_pre_hook] and [zify_post_hook] are there to be redefined. *)
Ltac zify_pre_hook := idtac.

Ltac zify_post_hook := idtac.

Ltac zify_convert_to_euclidean_division_equations_flag := constr:(false).

(** [zify_internal_to_euclidean_division_equations] is bound in [PreOmega] *)
Ltac zify_internal_to_euclidean_division_equations := idtac.

Ltac zify_to_euclidean_division_equations :=
  lazymatch zify_convert_to_euclidean_division_equations_flag with
  | true => zify_internal_to_euclidean_division_equations
  | false => idtac
  end.


Ltac zify := intros;
             zify_pre_hook ;
             zify_elim_let ;
             zify_op ;
             (zify_iter_specs) ;
             zify_saturate;
             zify_to_euclidean_division_equations ;
             zify_post_hook.
