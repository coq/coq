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

val infer_local_def : env -> Id.t -> section_def_entry ->
  constr * Sorts.relevance * types

val infer_local_assum : env -> types -> types * Sorts.relevance

val infer_primitive : env -> primitive_entry -> ('a, unit) pconstant_body

val infer_symbol : env -> symbol_entry -> ('a, unit) pconstant_body

val infer_parameter :
  sec_univs:UVars.Instance.t option -> env -> parameter_entry ->
    ('a, unit) pconstant_body

val infer_definition :
  sec_univs:UVars.Instance.t option -> env -> definition_entry ->
    HConstr.t option * ('a, unit) pconstant_body

val infer_opaque :
  sec_univs:UVars.Instance.t option -> env -> 'a opaque_entry ->
    (unit, unit) pconstant_body * typing_context

val check_delayed : 'a effect_handler -> typing_context -> 'a proof_output ->
  HConstr.t option * Constr.t * Univ.ContextSet.t Opaqueproof.delayed_universes
