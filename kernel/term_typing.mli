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
open Environ
open Declarations
open Entries

(** Handlers are used to manage side-effects. The ['a] type stands for the type
    of side-effects, and it is parametric because they are only defined later
    on. Handlers inline the provided side-effects into the term, and return
    the set of additional global constraints that need to be added for the term
    to be well typed. *)
type 'a effect_handler =
  env -> Constr.t -> 'a -> (Constr.t * Univ.ContextSet.t * int)

type _ trust =
| Pure : unit trust
| SideEffects : 'a effect_handler -> 'a trust

val translate_local_def : env -> Id.t -> section_def_entry ->
  constr * Sorts.relevance * types

val translate_local_assum : env -> types -> types * Sorts.relevance

val translate_constant :
  'a trust -> env -> Constant.t -> 'a constant_entry ->
    Opaqueproof.proofterm constant_body

val translate_recipe : env -> Constant.t -> Cooking.recipe -> Opaqueproof.opaque constant_body

(** Internal functions, mentioned here for debug purpose only *)

val infer_declaration : trust:'a trust -> env ->
  'a constant_entry -> Opaqueproof.proofterm Cooking.result

val build_constant_declaration :
  env -> Opaqueproof.proofterm Cooking.result -> Opaqueproof.proofterm constant_body
