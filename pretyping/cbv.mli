(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Identifier
open Names
open Term
open Evd
open Environ
open Closure
open Esubst
(*i*)

(***********************************************************************)
(*s Call-by-value reduction *)

(* Entry point for cbv normalization of a constr *)
type 'a cbv_infos
val create_cbv_infos : flags -> env -> 'a evar_map -> 'a cbv_infos
val cbv_norm : 'a cbv_infos -> constr -> constr

(***********************************************************************)
(*i This is for cbv debug *)
type cbv_value =
  | VAL of int * constr
  | LAM of name * constr * constr * cbv_value subs
  | FIXP of fixpoint * cbv_value subs * cbv_value list
  | COFIXP of cofixpoint * cbv_value subs * cbv_value list
  | CONSTR of int * inductive_path * cbv_value array * cbv_value list

val shift_value : int -> cbv_value -> cbv_value

type cbv_stack =
  | TOP
  | APP of cbv_value list * cbv_stack
  | CASE of constr * constr array * case_info * cbv_value subs * cbv_stack

val stack_app : cbv_value list -> cbv_stack -> cbv_stack
val under_case_stack : cbv_stack -> bool
val strip_appl : cbv_value -> cbv_stack -> cbv_value * cbv_stack

open RedFlags
val red_allowed : flags -> cbv_stack -> red_kind -> bool
val reduce_const_body :
  (cbv_value -> cbv_value) -> cbv_value -> cbv_stack -> cbv_value * cbv_stack

(* recursive functions... *)
val cbv_stack_term : 'a cbv_infos ->
  cbv_stack -> cbv_value subs -> constr -> cbv_value
val cbv_norm_term : 'a cbv_infos -> cbv_value subs -> constr -> constr
val cbv_norm_more : 'a cbv_infos -> cbv_value subs -> cbv_value -> cbv_value
val norm_head : 'a cbv_infos ->
  cbv_value subs -> constr -> cbv_stack -> cbv_value * cbv_stack
val apply_stack : 'a cbv_infos -> constr -> cbv_stack -> constr
val cbv_norm_value : 'a cbv_infos -> cbv_value -> constr
(* End of cbv debug section i*)
