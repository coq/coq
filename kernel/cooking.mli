(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

type abstr_info

(** The instantiation to apply to generalized declarations so that
    they behave as if not generalized: this is the a1..an instance to
    apply to a declaration c in the following transformation:
    [a1:T1..an:Tn, C:U(a1..an) ⊢ v(a1..an,C):V(a1..an,C)
     ~~>
     C:Πx1..xn.U(x1..xn), a1:T1..an:Tn ⊢ v(a1..an,Ca1..an):V(a1..an,Ca1..an)]
    note that the data looks close to the one for substitution above
    (because the substitution are represented by their domain) but
    here, local definitions of the context have been dropped *)

type abstr_inst_info = {
  abstr_inst : Constr.t array;
  (** The variables to reapply (excluding "let"s of the context) *)
  abstr_uinst : Univ.Instance.t;
  (** Abstracted universe variables to reapply *)
}

type 'a entry_map = 'a Cmap.t * 'a Mindmap.t
type expand_info = abstr_inst_info entry_map

(** The collection of instantiations to be done on generalized
    declarations + the generalization to be done on a specific
    judgment:
    [a1:T1,a2:T2,C:U(a1) ⊢ v(a1,a2,C):V(a1,a2,C)
     ~~>
     c:Πx.U(x) ⊢ λx1x2.(v(a1,a2,cx1)[a1,a2:=x1,x2]):Πx1x2.(V(a1,a2,ca1)[a1,a2:=x1,x2])]
    so, a cooking_info is the map [c ↦ x1..xn],
    the context x:T,y:U to generalize, and the substitution [x,y] *)

type cooking_info = {
  expand_info : expand_info;
  abstr_info : abstr_info;
  abstr_inst_info : abstr_inst_info; (* relevant for recursive types *)
  names_info : Id.Set.t; (* set of generalized names *)
}

val empty_cooking_info : cooking_info
  (** Nothing to abstract *)

val make_cooking_info : expand_info -> named_context -> Univ.UContext.t -> cooking_info
  (** Abstract a context assumed to be de-Bruijn free for terms and universes *)

val rel_context_of_cooking_info : cooking_info -> rel_context

val universe_context_of_cooking_info : cooking_info -> Univ.AbstractContext.t

val instance_of_cooking_info : cooking_info -> Constr.t array

type my_global_reference
module RefTable : Hashtbl.S with type key = my_global_reference

val abstract_as_type : abstr_inst_info RefTable.t -> cooking_info -> types -> types

val abstract_as_body : abstr_inst_info RefTable.t -> cooking_info -> constr -> constr

val abstract_as_sort : abstr_inst_info RefTable.t -> cooking_info -> Sorts.t -> Sorts.t

val lift_mono_univs : cooking_info -> Univ.ContextSet.t -> cooking_info * Univ.ContextSet.t

val lift_poly_univs : cooking_info -> Univ.AbstractContext.t -> cooking_info * Univ.AbstractContext.t

val lift_private_mono_univs : cooking_info -> 'a -> 'a

val lift_private_poly_univs : cooking_info -> Univ.ContextSet.t -> Univ.ContextSet.t

val discharge_proj_repr : cooking_info -> Names.Projection.Repr.t -> Names.Projection.Repr.t
