(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module implements pattern-matching on terms *)

open Names
open Term
open Environ
open Pattern

(** [PatternMatchingFailure] is the exception raised when pattern
  matching fails *)
exception PatternMatchingFailure

(** [special_meta] is the default name of the meta holding the
   surrounding context in subterm matching *)
val special_meta : metavariable

(** [bound_ident_map] represents the result of matching binding
   identifiers of the pattern with the binding identifiers of the term
   matched *)
type bound_ident_map = Id.t Id.Map.t

(** [matches pat c] matches [c] against [pat] and returns the resulting
   assignment of metavariables; it raises [PatternMatchingFailure] if
   not matchable; bindings are given in increasing order based on the
   numbers given in the pattern *)
val matches : env -> Evd.evar_map -> constr_pattern -> constr -> patvar_map

(** [matches_head pat c] does the same as [matches pat c] but accepts
    [pat] to match an applicative prefix of [c] *)
val matches_head : env -> Evd.evar_map -> constr_pattern -> constr -> patvar_map

(** [extended_matches pat c] also returns the names of bound variables
   in [c] that matches the bound variables in [pat]; if several bound
   variables or metavariables have the same name, the metavariable,
   or else the rightmost bound variable, takes precedence *)
val extended_matches :
  env -> Evd.evar_map -> constr_pattern -> constr -> bound_ident_map * extended_patvar_map

(** [is_matching pat c] just tells if [c] matches against [pat] *)
val is_matching : env -> Evd.evar_map -> constr_pattern -> constr -> bool

(** [is_matching_head pat c] just tells if [c] or an applicative
    prefix of it matches against [pat] *)
val is_matching_head : env -> Evd.evar_map -> constr_pattern -> constr -> bool

(** [matches_conv env sigma] matches up to conversion in environment
   [(env,sigma)] when constants in pattern are concerned; it raises
   [PatternMatchingFailure] if not matchable; bindings are given in
   increasing order based on the numbers given in the pattern *)
val matches_conv : env -> Evd.evar_map -> constr_pattern -> constr -> patvar_map

(** The type of subterm matching results: a substitution + a context
   (whose hole is denoted here with [special_meta]) *)
type matching_result =
    { m_sub : bound_ident_map * patvar_map;
      m_ctx : constr }

(** [match_subterm n pat c] returns the substitution and the context
   corresponding to each **closed** subterm of [c] matching [pat]. *)
val match_subterm : env -> Evd.evar_map -> constr_pattern -> constr -> matching_result IStream.t

(** [match_appsubterm pat c] returns the substitution and the context
   corresponding to each **closed** subterm of [c] matching [pat],
   considering application contexts as well. *)
val match_appsubterm : env -> Evd.evar_map -> constr_pattern -> constr -> matching_result IStream.t

(** [match_subterm_gen] calls either [match_subterm] or [match_appsubterm] *)
val match_subterm_gen : env -> Evd.evar_map -> bool (** true = with app context *) ->
   constr_pattern -> constr -> matching_result IStream.t

(** [is_matching_appsubterm pat c] tells if a subterm of [c] matches
   against [pat] taking partial subterms into consideration *)
val is_matching_appsubterm : ?closed:bool -> env -> Evd.evar_map -> constr_pattern -> constr -> bool

(** [is_matching_conv env sigma pat c] tells if [c] matches against [pat]
   up to conversion for constants in patterns *)
val is_matching_conv :
  env -> Evd.evar_map -> constr_pattern -> constr -> bool
