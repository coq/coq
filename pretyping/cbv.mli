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
  | LAM of int * (Name.t Context.binder_annot * constr) list * constr * cbv_value subs
  | FIXP of fixpoint * cbv_value subs * cbv_value array
  | COFIXP of cofixpoint * cbv_value subs * cbv_value array
  | CONSTR of constructor Univ.puniverses * cbv_value array
  | PRIMITIVE of CPrimitives.t * pconstant * cbv_value array
  | ARRAY of Univ.Instance.t * cbv_value Parray.t * cbv_value

and cbv_stack =
  | TOP
  | APP of cbv_value list * cbv_stack
  | CASE of Univ.Instance.t * constr array * case_return * case_branch array * Constr.case_invert * case_info * cbv_value subs * cbv_stack
  | PROJ of Projection.t * cbv_stack

val shift_value : int -> cbv_value -> cbv_value

val stack_app : cbv_value list -> cbv_stack -> cbv_stack
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
