(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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

type 'a delayed_universes =
| PrivateMonomorphic of 'a
| PrivatePolymorphic of int * Univ.ContextSet.t
  (** Number of surrounding bound universes + local constraints *)

type proofterm = (constr * Univ.ContextSet.t delayed_universes) Future.computation
type opaquetab
type opaque

val empty_opaquetab : opaquetab

(** From a [proofterm] to some [opaque]. *)
val create : proofterm -> opaque

(** Turn a direct [opaque] into an indirect one. It is your responsibility to
  hashcons the inner term beforehand. The integer is an hint of the maximum id
  used so far *)
val turn_indirect : DirPath.t -> opaque -> opaquetab -> opaque * opaquetab

type work_list = (Univ.Instance.t * Id.t array) Cmap.t *
  (Univ.Instance.t * Id.t array) Mindmap.t

type cooking_info = {
  modlist : work_list;
  abstract : Constr.named_context * Univ.Instance.t * Univ.AUContext.t }

type opaque_proofterm = cooking_info list * (Constr.t * unit delayed_universes) option

type indirect_accessor = {
  access_proof : DirPath.t -> int -> opaque_proofterm;
  access_discharge : cooking_info list ->
    (Constr.t * unit delayed_universes) -> (Constr.t * unit delayed_universes);
}
(** When stored indirectly, opaque terms are indexed by their library
    dirpath and an integer index. The two functions above activate
    this indirect storage, by telling how to retrieve terms.
*)

(** From a [opaque] back to a [constr]. This might use the
    indirect opaque accessor given as an argument. *)
val force_proof : indirect_accessor -> opaquetab -> opaque -> constr * unit delayed_universes
val force_constraints : indirect_accessor -> opaquetab -> opaque -> Univ.ContextSet.t
val get_direct_constraints : opaque -> Univ.ContextSet.t Future.computation

val subst_opaque : substitution -> opaque -> opaque

val discharge_direct_opaque :
  cooking_info -> opaque -> opaque

val join_opaque : ?except:Future.UUIDSet.t -> opaquetab -> opaque -> unit

val dump : ?except:Future.UUIDSet.t -> opaquetab ->
  opaque_proofterm array *
  int Future.UUIDMap.t
