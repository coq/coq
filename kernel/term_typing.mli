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

type typing_context

val translate_local_def : env -> Id.t -> section_def_entry ->
  constr * Sorts.relevance * types

val translate_local_assum : env -> types -> types * Sorts.relevance

val translate_constant :
  sec_univs:Univ.Level.t array option -> env -> Constant.t -> constant_entry ->
    'a pconstant_body

val translate_opaque :
  sec_univs:Univ.Level.t array option -> env -> Constant.t -> 'a opaque_entry ->
    unit pconstant_body * typing_context

val check_delayed : 'a effect_handler -> typing_context -> 'a proof_output -> (Constr.t * Univ.ContextSet.t Opaqueproof.delayed_universes)

(** Internal functions, mentioned here for debug purpose only *)

val infer_constant : sec_univs:Univ.Level.t array option -> env ->
  constant_entry -> typing_context Discharge.result

val build_constant_declaration :
  env -> 'a Discharge.result -> 'a pconstant_body
