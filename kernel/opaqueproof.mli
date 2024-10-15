(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Mod_subst

(** This module implements the handling of opaque proof terms.
    Opaque proof terms are special since:
    - they can be lazily computed and substituted
    - they are stored in an optionally loaded segment of .vo files
    An [opaque] proof terms holds an index into an opaque table. *)

type 'a delayed_universes =
| PrivateMonomorphic of 'a
| PrivatePolymorphic of Univ.ContextSet.t (** local constraints *)

type opaquetab
type opaque

val empty_opaquetab : opaquetab

val create : DirPath.t -> opaquetab -> opaque * opaquetab

type opaque_proofterm = Constr.t * unit delayed_universes

type opaque_handle

module HandleMap : CSig.MapS with type key = opaque_handle

(** Opaque terms are indexed by their library
    dirpath and an integer index. The two functions above activate
    this indirect storage, by telling how to retrieve terms.
*)

val subst_opaque : substitution -> opaque -> opaque

val discharge_opaque : Cooking.cooking_info -> opaque -> opaque

val repr_handle : opaque_handle -> int

val mem_handle : opaque_handle -> opaquetab -> bool

val repr : opaque -> substitution list * Cooking.cooking_info list * DirPath.t * opaque_handle
