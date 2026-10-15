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
  vm_reduce_blocks : bool;
  (** If false, preserve ordinary block-body syntax, but still force captured
      unblocks. The flag affects readback, not globally cached VM values. *)
}

val default_vm_flags : vm_flags

(** {6 Reduction functions } *)
val cbv_vm : ?flags:vm_flags -> env -> Evd.evar_map -> constr -> types -> constr
