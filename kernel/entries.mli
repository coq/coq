(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term

(** This module defines the entry types for global declarations. This
   information is entered in the environments. This includes global
   constants/axioms, mutual inductive definitions, modules and module
   types *)


(** {6 Local entries } *)

type local_entry =
  | LocalDef of constr
  | LocalAssum of constr


(** {6 Declaration of inductive types. } *)

(** Assume the following definition in concrete syntax:
{v Inductive I1 (x1:X1) ... (xn:Xn) : A1 := c11 : T11 | ... | c1n1 : T1n1
...
with      Ip (x1:X1) ... (xn:Xn) : Ap := cp1 : Tp1 | ... | cpnp : Tpnp. v}

then, in i{^ th} block, [mind_entry_params] is [xn:Xn;...;x1:X1];
[mind_entry_arity] is [Ai], defined in context [x1:X1;...;xn:Xn];
[mind_entry_lc] is [Ti1;...;Tini], defined in context [[A'1;...;A'p;x1:X1;...;xn:Xn]] where [A'i] is [Ai] generalized over [[x1:X1;...;xn:Xn]].
*)

type one_inductive_entry = {
  mind_entry_typename : Id.t;
  mind_entry_arity : constr;
  mind_entry_template : bool; (* Use template polymorphism *)
  mind_entry_consnames : Id.t list;
  mind_entry_lc : constr list }

type mutual_inductive_entry = {
  mind_entry_record : (Id.t option) option; 
  (** Some (Some id): primitive record with id the binder name of the record
      in projections.
      Some None: non-primitive record *)
  mind_entry_finite : Decl_kinds.recursivity_kind;
  mind_entry_params : (Id.t * local_entry) list;
  mind_entry_inds : one_inductive_entry list;
  mind_entry_polymorphic : bool; 
  mind_entry_universes : Univ.universe_context;
  mind_entry_private : bool option }

(** {6 Constants (Definition/Axiom) } *)
type proof_output = constr Univ.in_universe_context_set * Declareops.side_effects
type const_entry_body = proof_output Future.computation

type definition_entry = {
  const_entry_body   : const_entry_body;
  (* List of section variables *)
  const_entry_secctx : Context.section_context option;
  (* State id on which the completion of type checking is reported *)
  const_entry_feedback : Stateid.t option;
  const_entry_type        : types option;
  const_entry_polymorphic : bool;
  const_entry_universes   : Univ.universe_context;
  const_entry_opaque      : bool;
  const_entry_inline_code : bool }

type inline = int option (* inlining level, None for no inlining *)

type parameter_entry = 
    Context.section_context option * bool * types Univ.in_universe_context * inline 

type projection_entry = {
  proj_entry_ind : mutual_inductive;
  proj_entry_arg : int }

type constant_entry =
  | DefinitionEntry of definition_entry
  | ParameterEntry of parameter_entry
  | ProjectionEntry of projection_entry

(** {6 Modules } *)

type module_struct_entry = Declarations.module_alg_expr

type module_params_entry =
  (MBId.t * module_struct_entry) list (** older first *)

type module_type_entry = module_params_entry * module_struct_entry

type module_entry =
  | MType of module_params_entry * module_struct_entry
  | MExpr of
      module_params_entry * module_struct_entry * module_struct_entry option
