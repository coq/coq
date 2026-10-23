(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type axioms

val set_indirect_accessor : (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) -> unit

val check_module : Environ.env -> axioms -> Retroknowledge.action list -> Names.ModPath.t -> Mod_declarations.module_body -> axioms

exception BadConstant of Names.Constant.t * Pp.t

val constants_of_axioms : axioms -> Names.KerName.t list
val empty_axioms : axioms

(** Record assumptions hidden by module signatures without type checking. *)
val collect_module_axioms : axioms -> Names.ModPath.t -> Mod_declarations.module_body -> axioms
