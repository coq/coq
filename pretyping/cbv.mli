(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr
open Environ
open CClosure
open Esubst

(***********************************************************************
  s Call-by-value reduction *)

(** Entry point for cbv normalization of a constr *)
type cbv_infos

val create_cbv_infos : RedFlags.reds -> env -> Evd.evar_map -> cbv_infos
val cbv_norm         : cbv_infos -> constr -> constr

(***********************************************************************
  i This is for cbv debug *)

open Constr

type cbv_value =
  | VAL of int * constr
  | STACK of int * cbv_value * cbv_stack
  | CBN of constr * cbv_value subs
  | LAM of int * (Name.t * constr) list * constr * cbv_value subs
  | FIXP of fixpoint * cbv_value subs * cbv_value array
  | COFIXP of cofixpoint * cbv_value subs * cbv_value array
  | CONSTR of constructor Univ.puniverses * cbv_value array
  | PRIMITIVE of CPrimitives.t * Constr.t * cbv_value array

and cbv_stack =
  | TOP
  | APP of cbv_value array * cbv_stack
  | CASE of constr * constr array * case_info * cbv_value subs * cbv_stack
  | PROJ of Projection.t * cbv_stack

val shift_value : int -> cbv_value -> cbv_value

val stack_app : cbv_value array -> cbv_stack -> cbv_stack
val strip_appl : cbv_value -> cbv_stack -> cbv_value * cbv_stack

(** recursive functions... *)
val cbv_stack_term : cbv_infos ->
  cbv_stack -> cbv_value subs -> constr -> cbv_value
val cbv_norm_term : cbv_infos -> cbv_value subs -> constr -> constr
val norm_head : cbv_infos ->
  cbv_value subs -> constr -> cbv_stack -> cbv_value * cbv_stack
val apply_stack : cbv_infos -> constr -> cbv_stack -> constr
val cbv_norm_value : cbv_infos -> cbv_value -> constr

(** End of cbv debug section i*)
