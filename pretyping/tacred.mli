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

val is_evaluable : env -> evaluable_global_reference -> bool

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
val pattern_occs : (int list * constr) list ->  reduction_function
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

open Rawterm
(*
type red_expr =
  | Red of bool    (* raise Redelimination if true otherwise UserError *)
  | Hnf
  | Simpl
  | Cbv of Closure.RedFlags.reds
  | Lazy of Closure.RedFlags.reds
  | Unfold of (int list * evaluable_global_reference) list
  | Fold of constr list
  | Pattern of (int list * constr * constr) list
*)
type red_expr = (constr, evaluable_global_reference) red_expr_gen

val reduction_of_redexp : red_expr -> reduction_function

type generic_reduction_function = constr list -> reduction_function

val declare_red_expr : string -> generic_reduction_function -> unit

(* Opaque and Transparent commands. *)
val set_opaque_const      : constant -> unit
val set_transparent_const : constant -> unit

val set_opaque_var      : identifier -> unit
val set_transparent_var : identifier -> unit
