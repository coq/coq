(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr

(** This module defines the entry types for global declarations. This
   information is entered in the environments. This includes global
   constants/axioms, mutual inductive definitions, modules and module
   types *)


(** {6 Local entries } *)

type local_entry =
  | LocalDefEntry of constr
  | LocalAssumEntry of constr


(** {6 Declaration of inductive types. } *)

(** Assume the following definition in concrete syntax:
{v Inductive I1 (x1:X1) ... (xn:Xn) : A1 := c11 : T11 | ... | c1n1 : T1n1
...
with      Ip (x1:X1) ... (xn:Xn) : Ap := cp1 : Tp1 | ... | cpnp : Tpnp. v}

then, in i{^ th} block, [mind_entry_params] is [xn:Xn;...;x1:X1];
[mind_entry_arity] is [Ai], defined in context [x1:X1;...;xn:Xn];
[mind_entry_lc] is [Ti1;...;Tini], defined in context [[A'1;...;A'p;x1:X1;...;xn:Xn]] where [A'i] is [Ai] generalized over [[x1:X1;...;xn:Xn]].
*)

type inductive_universes =
  | Monomorphic_ind_entry of Univ.ContextSet.t
  | Polymorphic_ind_entry of Univ.UContext.t
  | Cumulative_ind_entry of Univ.CumulativityInfo.t

type one_inductive_entry = {
  mind_entry_typename : Id.t;
  mind_entry_arity : constr;
  mind_entry_template : bool; (* Use template polymorphism *)
  mind_entry_consnames : Id.t list;
  mind_entry_lc : constr list }

type mutual_inductive_entry = {
  mind_entry_record : (Id.t array option) option;
  (** Some (Some ids): primitive records with ids the binder name of each
      record in their respective projections. Not used by the kernel.
      Some None: non-primitive record *)
  mind_entry_finite : Declarations.recursivity_kind;
  mind_entry_params : (Id.t * local_entry) list;
  mind_entry_inds : one_inductive_entry list;
  mind_entry_universes : inductive_universes;
  (* universe constraints and the constraints for subtyping of
     inductive types in the block. *)
  mind_entry_private : bool option;
}

(** {6 Constants (Definition/Axiom) } *)
type 'a proof_output = constr Univ.in_universe_context_set * 'a
type 'a const_entry_body = 'a proof_output Future.computation

type constant_universes_entry =
  | Monomorphic_const_entry of Univ.ContextSet.t
  | Polymorphic_const_entry of Univ.UContext.t

type 'a in_constant_universes_entry = 'a * constant_universes_entry

type 'a definition_entry = {
  const_entry_body   : 'a const_entry_body;
  (* List of section variables *)
  const_entry_secctx : Constr.named_context option;
  (* State id on which the completion of type checking is reported *)
  const_entry_feedback : Stateid.t option;
  const_entry_type        : types option;
  const_entry_universes   : constant_universes_entry;
  const_entry_opaque      : bool;
  const_entry_inline_code : bool }

type section_def_entry = {
  secdef_body : constr;
  secdef_secctx : Constr.named_context option;
  secdef_feedback : Stateid.t option;
  secdef_type : types option;
}

type inline = int option (* inlining level, None for no inlining *)

type parameter_entry = 
    Constr.named_context option * types in_constant_universes_entry * inline

type 'a constant_entry =
  | DefinitionEntry of 'a definition_entry
  | ParameterEntry of parameter_entry

(** {6 Modules } *)

type module_struct_entry = Declarations.module_alg_expr

type module_params_entry =
  (MBId.t * module_struct_entry) list (** older first *)

type module_type_entry = module_params_entry * module_struct_entry

type module_entry =
  | MType of module_params_entry * module_struct_entry
  | MExpr of
      module_params_entry * module_struct_entry * module_struct_entry option


type seff_env =
  [ `Nothing
  (* The proof term and its universes.
     Same as the constant_body's but not in an ephemeron *)
  | `Opaque of Constr.t * Univ.ContextSet.t ]

(** Not used by the kernel. *)
type side_effect_role =
  | Subproof
  | Schema of inductive * string

type side_eff = {
  seff_constant : Constant.t;
  seff_body : Declarations.constant_body;
  seff_env : seff_env;
  seff_role : side_effect_role;
}
