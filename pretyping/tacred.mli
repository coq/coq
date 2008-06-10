(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Environ
open Evd
open Reductionops
open Closure
open Rawterm
open Termops
(*i*)

type reduction_tactic_error = 
    InvalidAbstraction of env * constr * (env * Type_errors.type_error)

exception ReductionTacticError of reduction_tactic_error

(*s Reduction functions associated to tactics. \label{tacred} *)

val is_evaluable : env -> evaluable_global_reference -> bool

exception Redelimination

(* Red (raise user error if nothing reducible) *)
val red_product : reduction_function

(* Red (raise Redelimination if nothing reducible) *)
val try_red_product : reduction_function

(* Simpl *)
val simpl : reduction_function 

(* Simpl only at the head *)
val whd_simpl : reduction_function

(* Hnf: like whd_simpl but force delta-reduction of constants that do
   not immediately hide a non reducible fix or cofix *)
val hnf_constr : reduction_function

(* Unfold *)
val unfoldn : 
  (occurrences * evaluable_global_reference) list ->  reduction_function

(* Fold *)
val fold_commands : constr list ->  reduction_function

(* Pattern *)
val pattern_occs : (occurrences * constr) list ->  reduction_function
(* Rem: Lazy strategies are defined in Reduction *)

(* Call by value strategy (uses Closures) *)
val cbv_norm_flags : Closure.RedFlags.reds ->  reduction_function
  val cbv_beta : local_reduction_function
  val cbv_betaiota : local_reduction_function
  val cbv_betadeltaiota :  reduction_function
  val compute :  reduction_function  (* = [cbv_betadeltaiota] *)

(* [reduce_to_atomic_ind env sigma t] puts [t] in the form [t'=(I args)]
   with [I] an inductive definition;
   returns [I] and [t'] or fails with a user error *)
val reduce_to_atomic_ind : env ->  evar_map -> types -> inductive * types

(* [reduce_to_quantified_ind env sigma t] puts [t] in the form
   [t'=(x1:A1)..(xn:An)(I args)] with [I] an inductive definition;
   returns [I] and [t'] or fails with a user error *)
val reduce_to_quantified_ind : env ->  evar_map -> types -> inductive * types

(* [reduce_to_quantified_ref env sigma ref t] try to put [t] in the form
   [t'=(x1:A1)..(xn:An)(ref args)] and raise [Not_found] if not possible *)
val reduce_to_quantified_ref :
  env ->  evar_map -> Libnames.global_reference -> types -> types

val reduce_to_atomic_ref :
  env ->  evar_map -> Libnames.global_reference -> types -> types

val contextually : bool -> occurrences * constr -> reduction_function
  -> reduction_function

(* Compatibility *)
(* use [simpl] instead of [nf] *)
val nf :  reduction_function

