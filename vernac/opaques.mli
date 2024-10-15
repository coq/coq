(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'a const_entry_body = 'a Entries.proof_output Future.computation

val declare_defined_opaque : ?feedback_id:Stateid.t ->
  Opaqueproof.opaque_handle -> Safe_typing.private_constants const_entry_body -> unit
val declare_private_opaque : Safe_typing.exported_opaque -> unit

type opaque_disk

val get_opaque_disk : Opaqueproof.opaque_handle -> opaque_disk -> Opaqueproof.opaque_proofterm option
val set_opaque_disk : Opaqueproof.opaque_handle -> Opaqueproof.opaque_proofterm -> opaque_disk -> unit

val get_current_opaque : Opaqueproof.opaque_handle -> Opaqueproof.opaque_proofterm option
val get_current_constraints : Opaqueproof.opaque_handle -> Univ.ContextSet.t option

val dump : ?except:Future.UUIDSet.t -> unit -> opaque_disk * Opaqueproof.opaque_handle Future.UUIDMap.t

module Summary :
sig
  type t
  val init : unit -> unit
  val freeze : unit -> t
  val unfreeze : t -> unit
  val join : ?except:Future.UUIDSet.t -> unit -> unit
end
