(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Constr
open Environ
open Declarations
open Entries

type side_effects

type _ trust =
| Pure : unit trust
| SideEffects : structure_body -> side_effects trust

val translate_local_def : env -> Id.t -> section_def_entry ->
  constr * types

val translate_local_assum : env -> types -> types

val mk_pure_proof : constr -> side_effects proof_output

val inline_side_effects : env -> constr -> side_effects -> constr
(** Returns the term where side effects have been turned into let-ins or beta
    redexes. *)

val inline_entry_side_effects :
  env -> side_effects definition_entry -> unit definition_entry
(** Same as {!inline_side_effects} but applied to entries. Only modifies the
    {!Entries.const_entry_body} field. It is meant to get a term out of a not
    yet type checked proof. *)

val empty_seff : side_effects
val add_seff : side_effect -> side_effects -> side_effects
val concat_seff : side_effects -> side_effects -> side_effects
(** [concat_seff e1 e2] adds the side-effects of [e1] to [e2], i.e. effects in
    [e1] must be more recent than those of [e2]. *)
val uniq_seff : side_effects -> side_effect list
(** Return the list of individual side-effects in the order of their
    creation. *)

val equal_eff : side_effect -> side_effect -> bool

val translate_constant :
  'a trust -> env -> Constant.t -> 'a constant_entry ->
    constant_body

type side_effect_role =
  | Subproof
  | Schema of inductive * string

type exported_side_effect = 
  Constant.t * constant_body * side_effect_role
  
(* Given a constant entry containing side effects it exports them (either
 * by re-checking them or trusting them).  Returns the constant bodies to
 * be pushed in the safe_env by safe typing.  The main constant entry
 * needs to be translated as usual after this step. *)
val export_side_effects :
  structure_body -> env -> side_effects definition_entry ->
    exported_side_effect list * unit definition_entry

val translate_mind :
  env -> MutInd.t -> mutual_inductive_entry -> mutual_inductive_body

val translate_recipe : env -> Constant.t -> Cooking.recipe -> constant_body

(** Internal functions, mentioned here for debug purpose only *)

val infer_declaration : trust:'a trust -> env ->
  'a constant_entry -> Cooking.result

val build_constant_declaration :
  Constant.t -> env -> Cooking.result -> constant_body
