(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ind_tables

(** Induction/recursion schemes *)

val optimize_non_type_induction_scheme : 
  'a Ind_tables.scheme_kind ->
  Indrec.dep_flag ->
  Sorts.family ->
  'b ->
  Names.inductive ->
  (Constr.constr * UState.t) * Safe_typing.private_constants

val rect_scheme_kind_from_prop : individual scheme_kind
val ind_scheme_kind_from_prop : individual scheme_kind
val rec_scheme_kind_from_prop : individual scheme_kind
val rect_scheme_kind_from_type : individual scheme_kind
val rect_dep_scheme_kind_from_type : individual scheme_kind
val ind_scheme_kind_from_type : individual scheme_kind
val ind_dep_scheme_kind_from_type : individual scheme_kind
val rec_scheme_kind_from_type : individual scheme_kind
val rec_dep_scheme_kind_from_type : individual scheme_kind


(** Case analysis schemes *)

val case_scheme_kind_from_type : individual scheme_kind
val case_scheme_kind_from_prop : individual scheme_kind
val case_dep_scheme_kind_from_type : individual scheme_kind
val case_dep_scheme_kind_from_type_in_prop : individual scheme_kind
val case_dep_scheme_kind_from_prop : individual scheme_kind
val case_dep_scheme_kind_from_prop_in_prop : individual scheme_kind
