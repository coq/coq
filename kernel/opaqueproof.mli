(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Mod_subst
open Int

(** This module implements the handling of opaque proof terms.
    Opauqe proof terms are special since:
    - they can be lazily computed and substituted
    - they are stoked in an optionally loaded segment of .vo files
    An [opaque] proof terms holds the real data until fully discharged.
    In this case it is called [direct].
    When it is [turn_indirect] the data is relocated to an opaque table
    and the [opaque] is turned into an index. *)

type proofterm = (constr * Univ.universe_context_set) Future.computation
type opaquetab
type opaque

val empty_opaquetab : opaquetab

(** From a [proofterm] to some [opaque]. *)
val create : proofterm -> opaque

(** Turn a direct [opaque] into an indirect one, also hashconses constr.
 *  The integer is an hint of the maximum id used so far *)
val turn_indirect : DirPath.t -> opaque -> opaquetab -> opaque * opaquetab

(** From a [opaque] back to a [constr]. This might use the
    indirect opaque accessor configured below. *)
val force_proof : opaquetab -> opaque -> constr
val force_constraints : opaquetab -> opaque -> Univ.universe_context_set
val get_proof : opaquetab -> opaque -> Term.constr Future.computation
val get_constraints :
  opaquetab -> opaque -> Univ.universe_context_set Future.computation option

val subst_opaque : substitution -> opaque -> opaque
val iter_direct_opaque : (constr -> unit) -> opaque -> opaque

type work_list = (Univ.Instance.t * Id.t array) Cmap.t * 
  (Univ.Instance.t * Id.t array) Mindmap.t

type cooking_info = { 
  modlist : work_list; 
  abstract : Context.named_context * Univ.universe_level_subst * Univ.UContext.t } 

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
  Univ.universe_context_set Future.computation array *
  cooking_info list array *
  int Future.UUIDMap.t

(** When stored indirectly, opaque terms are indexed by their library
    dirpath and an integer index. The following two functions activate
    this indirect storage, by telling how to store and retrieve terms.
    Default creator always returns [None], preventing the creation of
    any indirect link, and default accessor always raises an error.
*)

val set_indirect_opaque_accessor :
  (DirPath.t -> int -> Term.constr Future.computation) -> unit
val set_indirect_univ_accessor :
  (DirPath.t -> int -> Univ.universe_context_set Future.computation option) -> unit

