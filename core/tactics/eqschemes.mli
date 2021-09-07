(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file builds schemes relative to equality inductive types *)

open Ind_tables

(** Builds a left-to-right rewriting scheme for an equality type *)

val rew_l2r_dep_scheme_kind : individual scheme_kind
val rew_l2r_scheme_kind : individual scheme_kind
val rew_r2l_forward_dep_scheme_kind : individual scheme_kind
val rew_l2r_forward_dep_scheme_kind : individual scheme_kind
val rew_r2l_dep_scheme_kind : individual scheme_kind
val rew_r2l_scheme_kind : individual scheme_kind

(** Builds a symmetry scheme for a symmetrical equality type *)

val sym_scheme_kind : individual scheme_kind

val sym_involutive_scheme_kind : individual scheme_kind

(** Builds a congruence scheme for an equality type *)

val congr_scheme_kind : individual scheme_kind
