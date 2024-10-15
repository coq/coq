(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Locus

(** Utilities on or_var *)

val or_var_map : ('a -> 'b) -> 'a or_var -> 'b or_var

(** Utilities on occurrences *)

val occurrences_map :
  ('a list -> 'b list) -> 'a occurrences_gen -> 'b occurrences_gen

(** {6 Counting occurrences} *)

type occurrences_count
  (** A counter of occurrences associated to a list of occurrences *)

(** Three basic functions to initialize, count, and conclude a loop
    browsing over subterms *)

val initialize_occurrence_counter : occurrences -> occurrences_count
  (** Initialize an occurrence_counter *)

val update_occurrence_counter : occurrences_count -> bool * occurrences_count
  (** Increase the occurrence counter by one and tell if the current occurrence is selected *)

val check_used_occurrences : occurrences_count -> unit
  (** Increase the occurrence counter and tell if the current occurrence is selected *)

(** Auxiliary functions about occurrence counters *)

val current_occurrence : occurrences_count -> int
  (** Tell the value of the current occurrence *)

val occurrences_done : occurrences_count -> bool
  (** Tell if there are no more occurrences to select and if the loop
      can be shortcut *)

val more_specific_occurrences : occurrences_count -> bool
  (** Tell if there are no more occurrences to select (or unselect)
      and if an inner loop can be shortcut *)

(** {6 Miscellaneous} *)

val is_selected : int -> occurrences -> bool

val is_all_occurrences : 'a occurrences_gen -> bool

val error_invalid_occurrence : int list -> 'a

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
