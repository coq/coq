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
open Constr
open Environ
open Evd

(** Errors related to recursors building *)

type recursion_scheme_error =
  | NotAllowedCaseAnalysis of (*isrec:*) bool * Sorts.t * pinductive
  | NotMutualInScheme of inductive * inductive
  | NotAllowedDependentAnalysis of (*isrec:*) bool * inductive

exception RecursionSchemeError of recursion_scheme_error

(** Eliminations *)

type dep_flag = bool

(** Build a case analysis elimination scheme in some sort family *)

val build_case_analysis_scheme : env -> Evd.evar_map -> pinductive ->
      dep_flag -> Sorts.family -> evar_map * Constr.t

(** Build a dependent case elimination predicate unless type is in Prop
   or is a recursive record with primitive projections. *)

val build_case_analysis_scheme_default : env -> evar_map -> pinductive ->
      Sorts.family -> evar_map * Constr.t

(** Builds a recursive induction scheme (Peano-induction style) in the same
   sort family as the inductive family; it is dependent if not in Prop
   or a recursive record with primitive projections.  *)

val build_induction_scheme : env -> evar_map -> pinductive ->
      dep_flag -> Sorts.family -> evar_map * constr

(** Builds mutual (recursive) induction schemes *)

val build_mutual_induction_scheme :
  env -> evar_map -> ?force_mutual:bool ->
  (pinductive * dep_flag * Sorts.family) list -> evar_map * constr list

(** Scheme combinators *)

(** [weaken_sort_scheme env sigma eq s n c t] derives by subtyping from [c:t]
   whose conclusion is quantified on [Type i] at position [n] of [t] a
   scheme quantified on sort [s]. [set] asks for [s] be declared equal to [i],
  otherwise just less or equal to [i]. *)

val weaken_sort_scheme : env -> evar_map -> bool -> Sorts.t -> int -> constr -> types ->
  evar_map * types * constr

(** Recursor names utilities *)

val lookup_eliminator : inductive -> Sorts.family -> GlobRef.t
val elimination_suffix : Sorts.family -> string
val make_elimination_ident : Id.t -> Sorts.family -> Id.t

val case_suffix : string
