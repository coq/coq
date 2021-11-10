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
open Environ
open Evd
open EConstr
open Reductionops
open Pattern
open Locus
open Univ
open Ltac_pretype

(* XXX: Move to a module *)
type evaluable_global_reference =
  | EvalVarRef of Id.t
  | EvalConstRef of Constant.t

val eq_egr : evaluable_global_reference ->  evaluable_global_reference -> bool

(** Here the semantics is completely unclear.
   What does "Hint Unfold t" means when "t" is a parameter?
   Does the user mean "Unfold X.t" or does she mean "Unfold y"
   where X.t is later on instantiated with y? I choose the first
   interpretation (i.e. an evaluable reference is never expanded). *)
val subst_evaluable_reference :
  Mod_subst.substitution -> evaluable_global_reference -> evaluable_global_reference

type reduction_tactic_error =
    InvalidAbstraction of env * evar_map * constr * (env * Type_errors.type_error)

exception ReductionTacticError of reduction_tactic_error

(** {6 Reduction functions associated to tactics. } *)

(** Evaluable global reference *)

val is_evaluable : Environ.env -> evaluable_global_reference -> bool

val error_not_evaluable : GlobRef.t -> 'a

val evaluable_of_global_reference :
  Environ.env -> GlobRef.t -> evaluable_global_reference

val global_of_evaluable_reference :
  evaluable_global_reference -> GlobRef.t

exception Redelimination

(** Red (raise user error if nothing reducible) *)
val red_product : reduction_function

(** Red (raise Redelimination if nothing reducible) *)
val try_red_product : reduction_function

(** Simpl *)
val simpl : reduction_function

(** Simpl only at the head *)
val whd_simpl : reduction_function

(** Hnf: like whd_simpl but force delta-reduction of constants that do
   not immediately hide a non reducible fix or cofix *)
val hnf_constr : reduction_function

(** Unfold *)
val unfoldn :
  (occurrences * evaluable_global_reference) list ->  reduction_function

(** Fold *)
val fold_commands : constr list ->  reduction_function

(** Pattern *)
val pattern_occs : (occurrences * constr) list -> e_reduction_function

(** Rem: Lazy strategies are defined in Reduction *)

(** Call by value strategy (uses Closures) *)
val cbv_norm_flags : CClosure.RedFlags.reds ->  reduction_function
  val cbv_beta : reduction_function
  val cbv_betaiota : reduction_function
  val cbv_betadeltaiota :  reduction_function
  val compute :  reduction_function  (** = [cbv_betadeltaiota] *)

(** [reduce_to_atomic_ind env sigma t] puts [t] in the form [t'=(I args)]
   with [I] an inductive definition;
   returns [I] and [t'] or fails with a user error *)
val reduce_to_atomic_ind : env ->  evar_map -> types -> (inductive * EInstance.t) * types

(** [reduce_to_quantified_ind env sigma t] puts [t] in the form
   [t'=(x1:A1)..(xn:An)(I args)] with [I] an inductive definition;
   returns [I] and [t'] or fails with a user error *)
val reduce_to_quantified_ind : env ->  evar_map -> types -> (inductive * EInstance.t) * types

(** [reduce_to_quantified_ref env sigma ref t] try to put [t] in the form
   [t'=(x1:A1)..(xn:An)(ref args)] and fails with user error if not possible *)
val reduce_to_quantified_ref :
  env ->  evar_map -> GlobRef.t -> types -> types

val reduce_to_atomic_ref :
  env ->  evar_map -> GlobRef.t -> types -> types

val find_hnf_rectype :
  env ->  evar_map -> types -> (inductive * EInstance.t) * constr list

val contextually : bool -> occurrences * constr_pattern ->
  (patvar_map -> reduction_function) -> reduction_function

val e_contextually : bool -> occurrences * constr_pattern ->
  (patvar_map -> e_reduction_function) -> e_reduction_function

(** Returns the same inductive if it is allowed for pattern-matching
    raises an error otherwise. **)
val check_privacy : env -> inductive puniverses -> inductive puniverses

(** Returns the same inductive if it is not a primitive record
    raises an error otherwise. **)
val check_not_primitive_record : env -> inductive puniverses -> inductive puniverses
