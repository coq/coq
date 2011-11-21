(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Environ
open Evd
open Reductionops
open Closure
open Glob_term
open Termops
open Pattern
open Libnames

type reduction_tactic_error =
    InvalidAbstraction of env * constr * (env * Type_errors.type_error)

exception ReductionTacticError of reduction_tactic_error

(** {6 Reduction functions associated to tactics. {% \label{%}tacred{% }%} } *)

(** Evaluable global reference *)

val is_evaluable : Environ.env -> evaluable_global_reference -> bool

val error_not_evaluable : Libnames.global_reference -> 'a

val evaluable_of_global_reference :
  Environ.env -> Libnames.global_reference -> evaluable_global_reference

val global_of_evaluable_reference :
  evaluable_global_reference -> Libnames.global_reference

exception Redelimination

(** Red (raise user error if nothing reducible) *)
val red_product : reduction_function

(** Red (raise Redelimination if nothing reducible) *)
val try_red_product : reduction_function

(** Tune the behaviour of simpl for the given constant name *)
type simpl_flag = [ `SimplDontExposeCase | `SimplNeverUnfold ]

val set_simpl_behaviour :
  bool -> global_reference -> (int list * int * simpl_flag list) -> unit
val get_simpl_behaviour :
  global_reference -> (int list * int * simpl_flag list) option

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
val pattern_occs : (occurrences * constr) list ->  reduction_function

(** Rem: Lazy strategies are defined in Reduction *)

(** Call by value strategy (uses Closures) *)
val cbv_norm_flags : Closure.RedFlags.reds ->  reduction_function
  val cbv_beta : local_reduction_function
  val cbv_betaiota : local_reduction_function
  val cbv_betadeltaiota :  reduction_function
  val compute :  reduction_function  (** = [cbv_betadeltaiota] *)

(** [reduce_to_atomic_ind env sigma t] puts [t] in the form [t'=(I args)]
   with [I] an inductive definition;
   returns [I] and [t'] or fails with a user error *)
val reduce_to_atomic_ind : env ->  evar_map -> types -> inductive * types

(** [reduce_to_quantified_ind env sigma t] puts [t] in the form
   [t'=(x1:A1)..(xn:An)(I args)] with [I] an inductive definition;
   returns [I] and [t'] or fails with a user error *)
val reduce_to_quantified_ind : env ->  evar_map -> types -> inductive * types

(** [reduce_to_quantified_ref env sigma ref t] try to put [t] in the form
   [t'=(x1:A1)..(xn:An)(ref args)] and fails with user error if not possible *)
val reduce_to_quantified_ref :
  env ->  evar_map -> global_reference -> types -> types

val reduce_to_atomic_ref :
  env ->  evar_map -> global_reference -> types -> types

val contextually : bool -> occurrences * constr_pattern ->
  (patvar_map -> reduction_function) -> reduction_function
