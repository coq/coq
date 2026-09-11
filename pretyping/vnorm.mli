(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open EConstr
open Environ

type vm_flags = {
  vm_normalize_params : bool;
}

type readback_info = {
  readback_depth : int;
}

type readback_check = readback_info -> Environ.env -> Evd.evar_map -> types -> Vmvalues.kind -> unit

val no_readback_check : readback_check

(** {6 Reduction functions } *)
val cbv_vm : ?flags:vm_flags -> ?readback_check:readback_check -> env -> Evd.evar_map -> constr -> types -> constr
