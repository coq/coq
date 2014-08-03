(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Mod_subst

(** This module implements the handling of opaque proof terms.
    Opauqe proof terms are special since:
    - they can be lazily computed and substituted
    - they are stoked in an optionally loaded segment of .vo files
    An [opaque] proof terms holds the real data until fully discharged.
    In this case it is called [direct].
    When it is [turn_indirect] the data is relocated to an opaque table
    and the [opaque] is turned into an index. *)

type proofterm = (constr * Univ.universe_context_set) Future.computation
type opaque

(** From a [proofterm] to some [opaque]. *)
val create : proofterm -> opaque

(** Turn a direct [opaque] into an indirect one, also hashconses constr *)
val turn_indirect : opaque -> opaque

(** From a [opaque] back to a [constr]. This might use the
    indirect opaque accessor configured below. *)
val force_proof : opaque -> constr
val force_constraints : opaque -> Univ.universe_context_set
val get_proof : opaque -> Term.constr Future.computation
val get_constraints : opaque -> Univ.universe_context_set Future.computation option

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

val join_opaque : opaque -> unit

(** When stored indirectly, opaque terms are indexed by their library
    dirpath and an integer index. The following two functions activate
    this indirect storage, by telling how to store and retrieve terms.
    Default creator always returns [None], preventing the creation of
    any indirect link, and default accessor always raises an error.
*)

val set_indirect_creator :
  (cooking_info list * proofterm -> (DirPath.t * int) option) -> unit
val set_indirect_opaque_accessor :
  (DirPath.t -> int -> Term.constr Future.computation) -> unit
val set_indirect_univ_accessor :
  (DirPath.t -> int -> Univ.universe_context_set Future.computation option) -> unit
val set_join_indirect_local_opaque : (DirPath.t -> int -> unit) -> unit
val set_join_indirect_local_univ : (DirPath.t -> int -> unit) -> unit
val reset_indirect_creator : unit -> unit
