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
open Closure
open Esubst
(*i*)

(************************************************************************)
(*s Call-by-value reduction *)

(* Entry point for cbv normalization of a constr *)
type cbv_infos

val create_cbv_infos : RedFlags.reds -> env -> cbv_infos
val cbv_norm         : cbv_infos -> constr -> constr

(************************************************************************)
(*i This is for cbv debug *)
type cbv_value =
  | VAL of int * constr
  | LAM of int * (name * constr) list * constr * cbv_value subs
  | FIXP of fixpoint * cbv_value subs * cbv_value array
  | COFIXP of cofixpoint * cbv_value subs * cbv_value array
  | CONSTR of constructor * cbv_value array

val shift_value : int -> cbv_value -> cbv_value

type cbv_stack =
  | TOP
  | APP of cbv_value array * cbv_stack
  | CASE of constr * constr array * case_info * cbv_value subs * cbv_stack

val stack_app : cbv_value array -> cbv_stack -> cbv_stack
val strip_appl : cbv_value -> cbv_stack -> cbv_value * cbv_stack

(* recursive functions... *)
val cbv_stack_term : cbv_infos ->
  cbv_stack -> cbv_value subs -> constr -> cbv_value
val cbv_norm_term : cbv_infos -> cbv_value subs -> constr -> constr
val norm_head : cbv_infos ->
  cbv_value subs -> constr -> cbv_stack -> cbv_value * cbv_stack
val apply_stack : cbv_infos -> constr -> cbv_stack -> constr
val cbv_norm_value : cbv_infos -> cbv_value -> constr
(* End of cbv debug section i*)
