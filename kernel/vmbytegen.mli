(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vmbytecodes
open Vmemitcodes
open Constr
open Declarations
open Environ

(** Should only be used for monomorphic terms *)
val compile :
  fail_on_error:bool -> ?universes:int ->
  env -> (existential -> constr option) -> constr ->
  (to_patch * fv) option
(** init, fun, fv *)

val compile_constant_body : fail_on_error:bool ->
  env -> universes -> (Constr.t, 'opaque) constant_def ->
  body_code option

(** Shortcut of the previous function used during module strengthening *)

val compile_alias : Names.Constant.t -> body_code

(** Dump the bytecode after compilation (for debugging purposes) *)
val dump_bytecode : bool ref
