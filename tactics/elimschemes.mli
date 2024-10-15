(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ind_tables

(** Induction/recursion schemes *)

val elim_scheme : dep:bool -> to_kind:Sorts.family -> individual scheme_kind

(** Case analysis schemes *)

val case_dep : individual scheme_kind
val case_nodep : individual scheme_kind
val casep_dep : individual scheme_kind
val casep_nodep : individual scheme_kind
