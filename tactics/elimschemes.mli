(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Ind_tables

(** Induction/recursion schemes *)

val optimize_non_type_induction_scheme : 
  'a Ind_tables.scheme_kind ->
  Indrec.dep_flag ->
  Term.sorts_family ->
  'b ->
  Names.inductive ->
  (Constr.constr * Evd.evar_universe_context) * Safe_typing.private_constants

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
