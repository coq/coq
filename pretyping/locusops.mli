(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Locus

(** Utilities on occurrences *)

val occurrences_map :
  ('a list -> 'b list) -> 'a occurrences_gen -> 'b occurrences_gen

(** From occurrences to a list of positions (or complement of positions) *)
val convert_occs : occurrences -> bool * int list

val is_selected : int -> occurrences -> bool

(** Usual clauses *)

val allHypsAndConcl : 'a clause_expr
val allHyps : 'a clause_expr
val onConcl : 'a clause_expr
val nowhere : 'a clause_expr
val onHyp : 'a -> 'a clause_expr

(** Tests *)

val is_nowhere : 'a clause_expr -> bool

(** Clause conversion functions, parametrized by a hyp enumeration function *)

val simple_clause_of : (unit -> Id.t list) -> clause -> simple_clause
val concrete_clause_of : (unit -> Id.t list) -> clause -> concrete_clause

(** Miscellaneous functions *)

val occurrences_of_hyp : Id.t -> clause -> (occurrences * hyp_location_flag)
val occurrences_of_goal : clause -> occurrences
val in_every_hyp : clause -> bool

val clause_with_generic_occurrences : 'a clause_expr -> bool
val clause_with_generic_context_selection : 'a clause_expr -> bool
