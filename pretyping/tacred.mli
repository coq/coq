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
open Environ
open Evd
open EConstr
open Reductionops
open Pattern
open Locus
open Ltac_pretype

(** Here the semantics is completely unclear.
   What does "Hint Unfold t" means when "t" is a parameter?
   Does the user mean "Unfold X.t" or does she mean "Unfold y"
   where X.t is later on instantiated with y? I choose the first
   interpretation (i.e. an evaluable reference is never expanded). *)
val subst_evaluable_reference :
  Mod_subst.substitution -> Evaluable.t -> Evaluable.t

type reduction_tactic_error =
    InvalidAbstraction of env * evar_map * constr * (env * Type_errors.type_error)

type 'a change = NoChange | Changed of 'a
type change_function = env -> evar_map -> constr -> (evar_map * constr) change

exception ReductionTacticError of reduction_tactic_error

(** {6 Reduction functions associated to tactics. } *)

(** Evaluable global reference *)

val is_evaluable : Environ.env -> Evaluable.t -> bool

exception NotEvaluableRef of GlobRef.t
val error_not_evaluable : ?loc:Loc.t -> GlobRef.t -> 'a

val evaluable_of_global_reference :
  Environ.env -> GlobRef.t -> Evaluable.t
(** Fails on opaque constants and variables
    (both those without bodies and those marked Opaque in the conversion oracle). *)

val soft_evaluable_of_global_reference :
  ?loc:Loc.t -> GlobRef.t -> Evaluable.t
(** Succeeds for any constant or variable even if marked opaque or otherwise not evaluable. *)

val global_of_evaluable_reference :
  Evaluable.t -> GlobRef.t

(** Red (returns None if nothing reducible) *)
val red_product : env -> evar_map -> constr -> constr option

(** Simpl *)
val simpl : reduction_function

(** Simpl only at the head *)
val whd_simpl : reduction_function

(** Hnf: like whd_simpl but force delta-reduction of constants that do
   not immediately hide a non reducible fix or cofix *)
val hnf_constr : reduction_function

(** Variant of the above that does not perform nf-βι *)
val hnf_constr0 : reduction_function

(** Unfold *)
val unfoldn :
  (occurrences * Evaluable.t) list ->  reduction_function

(** Fold *)
val fold_commands : constr list ->  reduction_function

(** Pattern *)
val pattern_occs : (occurrences * constr) list -> change_function

(** Rem: Lazy strategies are defined in Reduction *)

(** Call by value strategy (uses Closures) *)
val cbv_norm_flags : RedFlags.reds -> strong:bool -> reduction_function
  val cbv_beta : reduction_function
  val cbv_betaiota : reduction_function
  val cbv_betadeltaiota :  reduction_function
  val whd_compute :  reduction_function
  val compute :  reduction_function  (** = [cbv_betadeltaiota] *)

(** [reduce_to_atomic_ind env sigma t] puts [t] in the form [t'=(I args)]
   with [I] an inductive definition;
   returns [I] and [t'] or fails with a user error *)
val reduce_to_atomic_ind : env ->  evar_map -> types -> (inductive * EInstance.t) * types

(** [reduce_to_quantified_ind env sigma t] puts [t] in the form
   [t'=(x1:A1)..(xn:An)(I args)] with [I] an inductive definition;
   returns [I] and [t'] or fails with a user error *)
val reduce_to_quantified_ind : env ->  evar_map -> types -> (inductive * EInstance.t) * types

(** Same as {!reduce_to_quantified_ind} but more efficient because it does not
    return the normalized type. *)
val eval_to_quantified_ind : env -> evar_map -> types -> (inductive * EInstance.t)

(** [reduce_to_quantified_ref env sigma ref t] try to put [t] in the form
    [t'=(x1:A1)..(xn:An)(ref args)]. When this is not possible, if [allow_failure]
    is specified, [t] is unfolded until the point where this impossibility is plainly
    visible. Otherwise, it fails with user error. *)
val reduce_to_quantified_ref :
  ?allow_failure:bool -> env ->  evar_map -> GlobRef.t -> types -> types

val reduce_to_atomic_ref :
  ?allow_failure:bool -> env ->  evar_map -> GlobRef.t -> types -> types

val find_hnf_rectype :
  env ->  evar_map -> types -> (inductive * EInstance.t) * constr list

val contextually : bool -> occurrences * constr_pattern ->
  (patvar_map -> reduction_function) -> reduction_function

val e_contextually : bool -> occurrences * constr_pattern ->
  (patvar_map -> change_function) -> change_function

(** Errors if the inductive is not allowed for pattern-matching. **)
val check_privacy : env -> inductive -> unit
