(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Environ
open Evd
open Reductionops
open Closure
(*i*)

(*s Reduction functions associated to tactics. \label{tacred} *)

exception Redelimination

(* Red (raise Redelimination if nothing reducible) *)
val red_product : reduction_function

(* Hnf *)
val hnf_constr :  reduction_function

(* Simpl *)
val nf :  reduction_function

(* Unfold *)
val unfoldn : 
  (int list * evaluable_global_reference) list ->  reduction_function

(* Fold *)
val fold_commands : constr list ->  reduction_function

(* Pattern *)
val pattern_occs : (int list * constr * constr) list ->  reduction_function
(* Rem: Lazy strategies are defined in Reduction *)

(* Call by value strategy (uses Closures) *)
val cbv_norm_flags : Closure.flags ->  reduction_function
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

type red_expr =
  | Red of bool    (* raise Redelimination if true otherwise UserError *)
  | Hnf
  | Simpl
  | Cbv of Closure.flags
  | Lazy of Closure.flags
  | Unfold of (int list * evaluable_global_reference) list
  | Fold of constr list
  | Pattern of (int list * constr * constr) list

val reduction_of_redexp : red_expr ->  reduction_function
