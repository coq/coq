(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Declarations

(** {6 Cooking the constants. } *)

type inline = bool

type 'opaque result = {
  cook_body : (constr, 'opaque) constant_def;
  cook_type : types;
  cook_universes : universes;
  cook_relevance : Sorts.relevance;
  cook_inline : inline;
  cook_context : Names.Id.Set.t option;
  cook_flags : typing_flags;
}

val make_cooking_info : expand_info -> named_context -> Univ.UContext.t -> cooking_info
  (** Abstract a context assumed to be de-Bruijn free for terms and universes *)

val cook_opaque_proofterm : cooking_info list ->
  Opaqueproof.opaque_proofterm -> Opaqueproof.opaque_proofterm

val cook_constant :
  Environ.env -> cooking_info -> constant_body -> constant_body

val cook_inductive :
  cooking_info -> mutual_inductive_body -> mutual_inductive_body

val lift_poly_univs : cooking_info -> Univ.AbstractContext.t -> cooking_info * Univ.AbstractContext.t

val cook_rel_context : cooking_info -> rel_context -> rel_context

val discharge_proj_repr : abstr_inst_info -> Names.Projection.Repr.t -> Names.Projection.Repr.t
