(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val set_indirect_accessor : (Opaqueproof.opaque -> Opaqueproof.opaque_proofterm) -> unit

val check_module : Environ.env -> Names.Cset.t Names.Cmap.t -> Names.ModPath.t -> Mod_declarations.module_body -> Names.Cset.t Names.Cmap.t

exception BadConstant of Names.Constant.t * Pp.t
