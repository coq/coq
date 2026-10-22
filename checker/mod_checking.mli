(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type opaques

val set_indirect_accessor : (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) -> unit

val check_module : Environ.env -> opaques -> Retroknowledge.action list -> Names.ModPath.t -> Mod_declarations.module_body -> opaques

exception BadConstant of Names.Constant.t * Pp.t

val constants_of_opaques : Environ.env -> opaques -> Names.Constant.t list
val empty_opaques : opaques

val use_async : bool ref
type 'a safe_queue
val await : (unit -> unit) safe_queue
val take : 'a safe_queue -> 'a option
val set_done : _ safe_queue -> unit
