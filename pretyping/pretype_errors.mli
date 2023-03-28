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
open EConstr
open Type_errors

(** {6 The type of errors raised by the pretyper } *)

type unification_error =
  | OccurCheck of Evar.t * constr
  | NotClean of existential * env * constr
  | NotSameArgSize
  | NotSameHead
  | NoCanonicalStructure
  | ConversionFailed of env * constr * constr
  | IncompatibleInstances of env * existential * constr * constr
  | MetaOccurInBody of Evar.t
  | InstanceNotSameType of Evar.t * env * types * types
  | InstanceNotFunctionalType of Evar.t * env * constr * types
  | UnifUnivInconsistency of UGraph.univ_inconsistency
  | CannotSolveConstraint of Evd.evar_constraint * unification_error
  | ProblemBeyondCapabilities

type position = (Id.t * Locus.hyp_location_flag) option

type position_reporting = (position * int) * constr

type subterm_unification_error = bool * position_reporting * position_reporting * (constr * constr * unification_error) option

type type_error = (constr, types) ptype_error

type pretype_error =
  | CantFindCaseType of constr
  (** Old Case *)

  | ActualTypeNotCoercible of unsafe_judgment * types * unification_error
  (** Type inference unification *)

  | UnifOccurCheck of Evar.t * constr
  (** Tactic Unification *)

  | UnsolvableImplicit of Evar.t * Evd.unsolvability_explanation option
  | CannotUnify of constr * constr * unification_error option
  | CannotUnifyLocal of constr * constr * constr
  | CannotUnifyBindingType of constr * constr
  | CannotGeneralize of constr
  | NoOccurrenceFound of constr * Id.t option
  | CannotFindWellTypedAbstraction of constr * constr list * (env * pretype_error) option
  | WrongAbstractionType of Name.t * constr * types * types
  | AbstractionOverMeta of Name.t * Name.t
  | NonLinearUnification of Name.t * constr
  (** Pretyping *)
  | VarNotFound of Id.t
  | EvarNotFound of Id.t
  | UnexpectedType of constr * constr * unification_error
  | NotProduct of constr
  | TypingError of type_error
  | CantApplyBadTypeExplained of (constr,types) pcant_apply_bad_type * unification_error
  | CannotUnifyOccurrences of subterm_unification_error
  | UnsatisfiableConstraints of
    (Evar.t * Evar_kinds.t) option * Evar.Set.t
    (** unresolvable evar, connex component *)
  | DisallowedSProp

exception PretypeError of env * Evd.evar_map * pretype_error

val precatchable_exception : exn -> bool

(** Raising errors *)
val error_actual_type :
  ?loc:Loc.t -> ?info:Exninfo.info -> env -> Evd.evar_map -> unsafe_judgment -> constr ->
      unification_error -> 'b

val error_actual_type_core :
  ?loc:Loc.t -> env -> Evd.evar_map -> unsafe_judgment -> constr -> 'b

val error_cant_apply_not_functional :
  ?loc:Loc.t -> env -> Evd.evar_map ->
      unsafe_judgment -> unsafe_judgment array -> 'b

val error_cant_apply_bad_type :
  ?loc:Loc.t -> env -> Evd.evar_map -> ?error:unification_error ->
  int * constr * constr ->
  unsafe_judgment -> unsafe_judgment array -> 'b

val error_case_not_inductive :
  ?loc:Loc.t -> env -> Evd.evar_map -> unsafe_judgment -> 'b

val error_ill_formed_branch :
  ?loc:Loc.t -> env -> Evd.evar_map ->
      constr -> pconstructor -> constr -> constr -> 'b

val error_number_branches :
  ?loc:Loc.t -> env -> Evd.evar_map ->
      unsafe_judgment -> int -> 'b

val error_ill_typed_rec_body :
  ?loc:Loc.t -> env -> Evd.evar_map ->
      int -> Name.t Context.binder_annot array -> unsafe_judgment array -> types array -> 'b

val error_elim_arity :
  ?loc:Loc.t -> env -> Evd.evar_map ->
      pinductive -> constr ->
      (unsafe_judgment * Sorts.family * Sorts.family * Sorts.family) option -> 'b

val error_not_a_type :
  ?loc:Loc.t -> env -> Evd.evar_map -> unsafe_judgment -> 'b

val error_assumption :
  ?loc:Loc.t -> env -> Evd.evar_map -> unsafe_judgment -> 'b

val error_cannot_coerce : env -> Evd.evar_map -> constr * constr -> 'b

(** {6 Implicit arguments synthesis errors } *)

val error_occur_check : env -> Evd.evar_map -> Evar.t -> constr -> 'b

val error_unsolvable_implicit :
  ?loc:Loc.t -> env -> Evd.evar_map -> Evar.t ->
      Evd.unsolvability_explanation option -> 'b

val error_cannot_unify : ?loc:Loc.t -> env -> Evd.evar_map ->
  ?reason:unification_error -> constr * constr -> 'b

val error_cannot_unify_local : env -> Evd.evar_map -> constr * constr * constr -> 'b

val error_cannot_find_well_typed_abstraction : env -> Evd.evar_map ->
      constr -> constr list -> (env * pretype_error) option -> 'b

val error_wrong_abstraction_type :  env -> Evd.evar_map ->
      Name.t -> constr -> types -> types -> 'b

val error_abstraction_over_meta : env -> Evd.evar_map ->
  metavariable -> metavariable -> 'b

val error_non_linear_unification : env -> Evd.evar_map ->
  metavariable -> constr -> 'b

(** {6 Ml Case errors } *)

val error_cant_find_case_type :
  ?loc:Loc.t -> env -> Evd.evar_map -> constr -> 'b

(** {6 Pretyping errors } *)

val error_unexpected_type :
  ?loc:Loc.t -> env -> Evd.evar_map -> constr -> constr -> unification_error -> 'b

val error_not_product :
  ?loc:Loc.t -> env -> Evd.evar_map -> constr -> 'b

val error_var_not_found : ?loc:Loc.t -> env -> Evd.evar_map -> Id.t -> 'b

val error_evar_not_found : ?loc:Loc.t -> env -> Evd.evar_map -> Id.t -> 'b

val error_disallowed_sprop : env -> Evd.evar_map -> 'a

(** {6 Typeclass errors } *)

val unsatisfiable_constraints : env -> Evd.evar_map -> Evar.t option ->
  Evar.Set.t -> 'a

val unsatisfiable_exception : exn -> bool

