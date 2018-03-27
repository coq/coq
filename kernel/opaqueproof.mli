(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Mod_subst

(** This module implements the handling of opaque proof terms.
    Opaque proof terms are special since:
    - they can be lazily computed and substituted
    - they are stored in an optionally loaded segment of .vo files
    An [opaque] proof terms holds the real data until fully discharged.
    In this case it is called [direct].
    When it is [turn_indirect] the data is relocated to an opaque table
    and the [opaque] is turned into an index. *)

type proofterm = (constr * Univ.ContextSet.t) Future.computation
type opaquetab
type opaque

val empty_opaquetab : opaquetab

(** From a [proofterm] to some [opaque]. *)
val create : proofterm -> opaque

(** Turn a direct [opaque] into an indirect one. It is your responsibility to
  hashcons the inner term beforehand. The integer is an hint of the maximum id
  used so far *)
val turn_indirect : DirPath.t -> opaque -> opaquetab -> opaque * opaquetab

(** From a [opaque] back to a [constr]. This might use the
    indirect opaque accessor configured below. *)
val force_proof : opaquetab -> opaque -> constr
val force_constraints : opaquetab -> opaque -> Univ.ContextSet.t
val get_proof : opaquetab -> opaque -> constr Future.computation
val get_constraints :
  opaquetab -> opaque -> Univ.ContextSet.t Future.computation option

val subst_opaque : substitution -> opaque -> opaque
val iter_direct_opaque : (constr -> unit) -> opaque -> opaque

type work_list = (Univ.Instance.t * Id.t array) Cmap.t * 
  (Univ.Instance.t * Id.t array) Mindmap.t

type cooking_info = { 
  modlist : work_list; 
  abstract : Constr.named_context * Univ.Instance.t * Univ.AUContext.t }

(* The type has two caveats:
   1) cook_constr is defined after
   2) we have to store the input in the [opaque] in order to be able to
      discharge it when turning a .vi into a .vo *)
val discharge_direct_opaque :
  cook_constr:(constr -> constr) -> cooking_info -> opaque -> opaque

val uuid_opaque : opaquetab -> opaque -> Future.UUID.t option
val join_opaque : opaquetab -> opaque -> unit

val dump : opaquetab ->
  Constr.t Future.computation array *
  Univ.ContextSet.t Future.computation array *
  cooking_info list array *
  int Future.UUIDMap.t

(** When stored indirectly, opaque terms are indexed by their library
    dirpath and an integer index. The following two functions activate
    this indirect storage, by telling how to store and retrieve terms.
    Default creator always returns [None], preventing the creation of
    any indirect link, and default accessor always raises an error.
*)

val set_indirect_opaque_accessor :
  (DirPath.t -> int -> constr Future.computation) -> unit
val set_indirect_univ_accessor :
  (DirPath.t -> int -> Univ.ContextSet.t Future.computation option) -> unit

