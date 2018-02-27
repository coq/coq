(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Locus
open Evd
open Pretype_errors
open Environ
open EConstr

(** Finding subterms, possibly up to some unification function,
    possibly at some given occurrences *)

exception NotUnifiable of (constr * constr * unification_error) option

exception SubtermUnificationError of subterm_unification_error

(** A testing function is typically a unification function returning a
    substitution or failing with a NotUnifiable error, together with a
    function to merge substitutions and an initial substitution;
    last_found is used for error messages and it has to be initialized
    with None. *)

type 'a testing_function = {
  match_fun : 'a -> constr -> 'a;
  merge_fun : 'a -> 'a -> 'a;
  mutable testing_state : 'a;
  mutable last_found : position_reporting option
}

(** This is the basic testing function, looking for exact matches of a
    closed term *)
val make_eq_univs_test : env -> evar_map -> constr -> evar_map testing_function

(** [replace_term_occ_modulo occl test mk c] looks in [c] for subterm
    modulo a testing function [test] and replaces successfully
    matching subterms at the indicated occurrences [occl] with [mk
    ()]; it turns a NotUnifiable exception raised by the testing
    function into a SubtermUnificationError. *)
val replace_term_occ_modulo : evar_map -> occurrences or_like_first ->
  'a testing_function -> (unit -> constr) -> constr -> constr

(** [replace_term_occ_decl_modulo] is similar to
    [replace_term_occ_modulo] but for a named_declaration. *)
val replace_term_occ_decl_modulo :
  evar_map ->
  (occurrences * hyp_location_flag) or_like_first ->
  'a testing_function -> (unit -> constr) ->
  named_declaration -> named_declaration

(** [subst_closed_term_occ occl c d] replaces occurrences of
    closed [c] at positions [occl] by [Rel 1] in [d] (see also Note OCC),
    unifying universes which results in a set of constraints. *)
val subst_closed_term_occ : env -> evar_map -> occurrences or_like_first ->
  constr -> constr -> constr * evar_map

(** [subst_closed_term_occ_decl evd occl c decl] replaces occurrences of 
    closed [c] at positions [occl] by [Rel 1] in [decl]. *)
val subst_closed_term_occ_decl : env -> evar_map ->
  (occurrences * hyp_location_flag) or_like_first ->
  constr -> named_declaration -> named_declaration * evar_map

(** Miscellaneous *)
val error_invalid_occurrence : int list -> 'a
