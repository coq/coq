(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val set_local_flags : Declarations.typing_flags -> Environ.env -> Environ.env
(** Set flags except for those ignored by the checker (see .ml file for those). *)

(** Whether the user asked for the VM, i.e. the value of -bytecode-compiler. *)
val enable_vm : bool ref

(** Whether axioms and unsafe typing flags must be rejected (-axiom-free). *)
val axiom_free : bool ref

val is_axiom_free : Environ.env -> Names.Constant.t list -> bool
