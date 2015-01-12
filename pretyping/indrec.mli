(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Environ
open Evd

(** Errors related to recursors building *)

type recursion_scheme_error =
  | NotAllowedCaseAnalysis of (*isrec:*) bool * sorts * pinductive
  | NotMutualInScheme of inductive * inductive

exception RecursionSchemeError of recursion_scheme_error

(** Eliminations *)

type dep_flag = bool

(** Build a case analysis elimination scheme in some sort family *)

val build_case_analysis_scheme : env -> evar_map -> pinductive ->
      dep_flag -> sorts_family -> evar_map * constr

(** Build a dependent case elimination predicate unless type is in Prop *)

val build_case_analysis_scheme_default : env -> evar_map -> pinductive ->
      sorts_family -> evar_map * constr

(** Builds a recursive induction scheme (Peano-induction style) in the same
   sort family as the inductive family; it is dependent if not in Prop *)

val build_induction_scheme : env -> evar_map -> pinductive ->
      dep_flag -> sorts_family -> evar_map * constr

(** Builds mutual (recursive) induction schemes *)

val build_mutual_induction_scheme :
  env -> evar_map -> (pinductive * dep_flag * sorts_family) list -> evar_map * constr list

(** Scheme combinators *)

(** [weaken_sort_scheme env sigma eq s n c t] derives by subtyping from [c:t]
   whose conclusion is quantified on [Type i] at position [n] of [t] a
   scheme quantified on sort [s]. [set] asks for [s] be declared equal to [i],
  otherwise just less or equal to [i]. *)

val weaken_sort_scheme : env -> evar_map -> bool -> sorts -> int -> constr -> types -> 
  evar_map * types * constr

(** Recursor names utilities *)

val lookup_eliminator : inductive -> sorts_family -> Globnames.global_reference
val elimination_suffix : sorts_family -> string
val make_elimination_ident : Id.t -> sorts_family -> Id.t

val case_suffix : string
