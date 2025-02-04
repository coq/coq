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
open Constr

(** {6 Data needed to abstract over the section variables and section universes } *)

(** The instantiation to apply to generalized declarations so that
    they behave as if not generalized: this is the a1..an instance to
    apply to a declaration c in the following transformation:
    [a1:T1..an:Tn, C:U(a1..an) ⊢ v(a1..an,C):V(a1..an,C)
     ~~>
     C:Πx1..xn.U(x1..xn), a1:T1..an:Tn ⊢ v(a1..an,Ca1..an):V(a1..an,Ca1..an)]
    note that the data looks close to the one for substitution above
    (because the substitution are represented by their domain) but
    here, local definitions of the context have been dropped *)

type abstr_inst_info

type 'a entry_map = 'a Cmap_env.t * 'a Mindmap_env.t
type expand_info = abstr_inst_info entry_map

(** The collection of instantiations to be done on generalized
    declarations + the generalization to be done on a specific
    judgment:
    [a1:T1,a2:T2,C:U(a1) ⊢ v(a1,a2,C):V(a1,a2,C)
     ~~>
     c:Πx.U(x) ⊢ λx1x2.(v(a1,a2,cx1)[a1,a2:=x1,x2]):Πx1x2.(V(a1,a2,ca1)[a1,a2:=x1,x2])]
    so, a cooking_info is the map [c ↦ x1..xn],
    the context x:T,y:U to generalize, and the substitution [x,y] *)

type cooking_info

val empty_cooking_info : cooking_info
  (** Nothing to abstract *)

val make_cooking_info : recursive:MutInd.t option -> expand_info ->
  named_context -> UVars.UContext.t -> cooking_info * abstr_inst_info
(** Abstract a context assumed to be de-Bruijn free for terms and universes *)

val names_info : cooking_info -> Id.Set.t

val universe_context_of_cooking_info : cooking_info -> UVars.AbstractContext.t

val instance_of_cooking_info : cooking_info -> Constr.t array

type cooking_cache

val create_cache : cooking_info -> cooking_cache
val instance_of_cooking_cache : cooking_cache -> Constr.t array
val rel_context_of_cooking_cache : cooking_cache -> rel_context

val abstract_as_type : cooking_cache -> types -> types

val abstract_as_body : cooking_cache -> constr -> constr

val abstract_as_sort : cooking_cache -> Sorts.t -> Sorts.t

val lift_mono_univs : cooking_info -> Univ.ContextSet.t -> cooking_info * Univ.ContextSet.t

(** The [int] is how many universes got discharged, ie size of
    returned context - size of input context. *)
val lift_poly_univs : cooking_info -> UVars.AbstractContext.t -> cooking_info * (int * int) * UVars.AbstractContext.t

val lift_private_mono_univs : cooking_info -> 'a -> 'a

val lift_private_poly_univs : cooking_info -> Univ.ContextSet.t -> Univ.ContextSet.t

val discharge_proj_repr : cooking_info -> Names.Projection.Repr.t -> Names.Projection.Repr.t
