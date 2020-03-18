(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ind_tables

(** Induction/recursion schemes *)

val rect_scheme_kind_from_prop : individual scheme_kind
val ind_scheme_kind_from_prop : individual scheme_kind
val sind_scheme_kind_from_prop : individual scheme_kind
val rec_scheme_kind_from_prop : individual scheme_kind
val rect_scheme_kind_from_type : individual scheme_kind
val rect_dep_scheme_kind_from_type : individual scheme_kind
val ind_scheme_kind_from_type : individual scheme_kind
val ind_dep_scheme_kind_from_type : individual scheme_kind
val sind_scheme_kind_from_type : individual scheme_kind
val sind_dep_scheme_kind_from_type : individual scheme_kind
val rec_scheme_kind_from_type : individual scheme_kind
val rec_dep_scheme_kind_from_type : individual scheme_kind

val nondep_elim_scheme : Sorts.family -> Sorts.family -> individual scheme_kind

(** Case analysis schemes *)

val case_scheme_kind_from_type : individual scheme_kind
val case_scheme_kind_from_prop : individual scheme_kind
val case_dep_scheme_kind_from_type : individual scheme_kind
val case_dep_scheme_kind_from_type_in_prop : individual scheme_kind
val case_dep_scheme_kind_from_prop : individual scheme_kind
val case_dep_scheme_kind_from_prop_in_prop : individual scheme_kind
