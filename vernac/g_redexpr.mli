(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Procq
open Genredexpr

val int_or_var : int Locus.or_var Entry.t
val nat_or_var : int Locus.or_var Entry.t
val pattern_occ : r_trm Locus.with_occurrences_expr Entry.t
val unfold_occ : r_cst Locus.with_occurrences_expr Entry.t
val ref_or_pattern_occ : (r_cst,r_pat) Util.union Locus.with_occurrences_expr Entry.t
val occs_nums : Locus.occurrences_expr Entry.t
val occs : Locus.occurrences_expr Entry.t
val delta_flag : r_cst red_atom Entry.t
val strategy_flag : r_cst glob_red_flag Entry.t
