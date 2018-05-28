(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Cbytecodes
open Cemitcodes
open Constr
open Declarations
open Environ

(** Should only be used for monomorphic terms *)
val compile : fail_on_error:bool ->
	      ?universes:int -> env -> constr -> (bytecodes * bytecodes * fv) option
(** init, fun, fv *)

val compile_constant_body : fail_on_error:bool ->
			    env -> constant_universes -> constant_def -> body_code option

(** Shortcut of the previous function used during module strengthening *)

val compile_alias : Names.Constant.t -> body_code

(** Dump the bytecode after compilation (for debugging purposes) *)
val dump_bytecode : bool ref
