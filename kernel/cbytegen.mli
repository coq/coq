(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Cbytecodes
open Cemitcodes
open Constr
open Declarations
open Pre_env

(** Should only be used for monomorphic terms *)
val compile : fail_on_error:bool ->
	      ?universes:int -> env -> constr -> (bytecodes * bytecodes * fv) option
(** init, fun, fv *)

val compile_constant_body : fail_on_error:bool ->
			    env -> constant_universes -> constant_def -> body_code option

(** Shortcut of the previous function used during module strengthening *)

val compile_alias : Names.Constant.t -> body_code
