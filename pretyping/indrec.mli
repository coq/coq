(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

exception RecursionSchemeError of env * recursion_scheme_error

(** Eliminations *)

type dep_flag = bool

(** Build a case analysis elimination scheme in some sort *)

type case_analysis = private {
  case_params : EConstr.rel_context;
  case_pred : Name.t Context.binder_annot * EConstr.types;
  case_branches : EConstr.rel_context;
  case_arity : EConstr.rel_context;
  case_body : EConstr.t;
  case_type : EConstr.t;
}

val check_valid_elimination : env -> evar_map -> pinductive -> dep:bool -> EConstr.ESorts.t -> unit

val eval_case_analysis : case_analysis -> EConstr.t * EConstr.types

val default_case_analysis_dependence : env -> inductive -> bool

val build_case_analysis_scheme : env -> Evd.evar_map -> pinductive ->
  dep_flag -> EConstr.ESorts.t -> evar_map * case_analysis

(** Build a dependent case elimination predicate unless type is in Prop
   or is a recursive record with primitive projections. *)

val build_case_analysis_scheme_default : env -> evar_map -> pinductive ->
      EConstr.ESorts.t -> evar_map * case_analysis

(** Builds a recursive induction scheme (Peano-induction style) in the given sort.  *)

val build_induction_scheme : env -> evar_map -> pinductive ->
      dep_flag -> EConstr.ESorts.t -> evar_map * constr

(** Builds mutual (recursive) induction schemes *)

val build_mutual_induction_scheme :
  env -> evar_map -> ?force_mutual:bool ->
  (pinductive * dep_flag * EConstr.ESorts.t) list -> evar_map * constr list

(** Recursor names utilities *)

val lookup_eliminator : env -> inductive -> Sorts.family -> GlobRef.t
val elimination_suffix : Sorts.family -> string
val make_elimination_ident : Id.t -> Sorts.family -> Id.t

val case_suffix : string

(** Default dependence of eliminations for Prop inductives *)

val declare_prop_but_default_dependent_elim : inductive -> unit

val is_prop_but_default_dependent_elim : inductive -> bool

val pseudo_sort_family_for_elim : inductive -> Declarations.one_inductive_body -> Sorts.family
