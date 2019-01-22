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

(** {6 Declaration of inductive types. } *)

(** Assume the following definition in concrete syntax:
{v Inductive I1 (x1:X1) ... (xn:Xn) : A1 := c11 : T11 | ... | c1n1 : T1n1
...
with      Ip (x1:X1) ... (xn:Xn) : Ap := cp1 : Tp1 | ... | cpnp : Tpnp. v}

then, in i{^ th} block, [mind_entry_params] is [xn:Xn;...;x1:X1];
[mind_entry_arity] is [Ai], defined in context [x1:X1;...;xn:Xn];
[mind_entry_lc] is [Ti1;...;Tini], defined in context [[A'1;...;A'p;x1:X1;...;xn:Xn]] where [A'i] is [Ai] generalized over [[x1:X1;...;xn:Xn]].
*)

type universe_entry = {
  entry_monomorphic_univs : Univ.ContextSet.t;
  entry_poly_univ_names : Name.t array;
  entry_polymorphic_univs : Univ.UContext.t;
  entry_is_polymorphic : bool; (* ignored by the kernel *)
}

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
  mind_entry_params : Constr.rel_context;
  mind_entry_inds : one_inductive_entry list;
  mind_entry_universes : universe_entry;
  mind_entry_variance : Univ.Variance.t array option;
  (* universe constraints and the constraints for subtyping of
     inductive types in the block. *)
  mind_entry_private : bool option;
}

(** {6 Constants (Definition/Axiom) } *)
type proof_body = {
  proof_body : constr;
  proof_univs : Univ.ContextSet.t;
  proof_priv_univs : Univ.ContextSet.t; (* should be empty if transparent constant *)
}
type 'a proof_output = proof_body * 'a
type 'a const_entry_body = 'a proof_output Future.computation

type 'a definition_entry = {
  const_entry_body   : 'a const_entry_body;
  (* List of section variables *)
  const_entry_secctx : Constr.named_context option;
  (* State id on which the completion of type checking is reported *)
  const_entry_feedback : Stateid.t option;
  const_entry_type        : types option;
  const_entry_universes   : universe_entry;
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
    Constr.named_context option * universe_entry * types * inline

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
