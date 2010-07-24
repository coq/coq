(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Univ
open Term
open Cemitcodes
open Sign
open Mod_subst

(** This module defines the internal representation of global
   declarations. This includes global constants/axioms, mutual
   inductive definitions, modules and module types *)

type engagement = ImpredicativeSet

(** {6 Representation of constants (Definition/Axiom) } *)

type polymorphic_arity = {
  poly_param_levels : universe option list;
  poly_level : universe;
}

type constant_type =
  | NonPolymorphicType of types
  | PolymorphicArity of rel_context * polymorphic_arity

type constr_substituted

val from_val : constr -> constr_substituted
val force : constr_substituted -> constr

type constant_body = {
    const_hyps : section_context; (** New: younger hyp at top *)
    const_body : constr_substituted option;
    const_type : constant_type;
    const_body_code : to_patch_substituted;
   (* const_type_code : to_patch;*)
    const_constraints : constraints;
    const_opaque : bool;
    const_inline : bool}

val subst_const_body : substitution -> constant_body -> constant_body

(** {6 Representation of mutual inductive types in the kernel } *)

type recarg =
  | Norec
  | Mrec of inductive
  | Imbr of inductive

val subst_recarg : substitution -> recarg -> recarg

type wf_paths = recarg Rtree.t

val mk_norec : wf_paths
val mk_paths : recarg -> wf_paths list array -> wf_paths
val dest_recarg : wf_paths -> recarg
val dest_subterms : wf_paths -> wf_paths list array
val recarg_length : wf_paths -> int -> int

val subst_wf_paths : substitution -> wf_paths -> wf_paths

(**
{v
   Inductive I1 (params) : U1 := c11 : T11 | ... | c1p1 : T1p1
   ...
   with      In (params) : Un := cn1 : Tn1 | ... | cnpn : Tnpn
v}
*)

type monomorphic_inductive_arity = {
  mind_user_arity : constr;
  mind_sort : sorts;
}

type inductive_arity =
| Monomorphic of monomorphic_inductive_arity
| Polymorphic of polymorphic_arity

type one_inductive_body = {
(** {8 Primitive datas } *)

    mind_typename : identifier; (** Name of the type: [Ii] *)

    mind_arity_ctxt : rel_context; (** Arity context of [Ii] with parameters: [forall params, Ui] *)

    mind_arity : inductive_arity; (** Arity sort and original user arity if monomorphic *)

    mind_consnames : identifier array; (** Names of the constructors: [cij] *)

    mind_user_lc : types array;
 (** Types of the constructors with parameters:  [forall params, Tij],
     where the Ik are replaced by de Bruijn index in the
     context I1:forall params, U1 ..  In:forall params, Un *)

(** {8 Derived datas } *)

    mind_nrealargs : int; (** Number of expected real arguments of the type (no let, no params) *)

    mind_nrealargs_ctxt : int; (** Length of realargs context (with let, no params) *)

    mind_kelim : sorts_family list; (** List of allowed elimination sorts *)

    mind_nf_lc : types array; (** Head normalized constructor types so that their conclusion is atomic *)

    mind_consnrealdecls : int array;
 (** Length of the signature of the constructors (with let, w/o params)
    (not used in the kernel) *)

    mind_recargs : wf_paths; (** Signature of recursive arguments in the constructors *)

(** {8 Datas for bytecode compilation } *)

    mind_nb_constant : int; (** number of constant constructor *)

    mind_nb_args : int; (** number of no constant constructor *)

    mind_reloc_tbl :  Cbytecodes.reloc_table;
  }

type mutual_inductive_body = {

    mind_packets : one_inductive_body array;  (** The component of the mutual inductive block *)

    mind_record : bool;  (** Whether the inductive type has been declared as a record *)

    mind_finite : bool;  (** Whether the type is inductive or coinductive *)

    mind_ntypes : int;  (** Number of types in the block *)

    mind_hyps : section_context;  (** Section hypotheses on which the block depends *)

    mind_nparams : int;  (** Number of expected parameters *)

    mind_nparams_rec : int;  (** Number of recursively uniform (i.e. ordinary) parameters *)

    mind_params_ctxt : rel_context;  (** The context of parameters (includes let-in declaration) *)

    mind_constraints : constraints;  (** Universes constraints enforced by the inductive declaration *)

  }

val subst_mind : substitution -> mutual_inductive_body -> mutual_inductive_body

(** {6 Modules: signature component specifications, module types, and
  module declarations } *)

type structure_field_body =
  | SFBconst of constant_body
  | SFBmind of mutual_inductive_body
  | SFBmodule of module_body
  | SFBmodtype of module_type_body

and structure_body = (label * structure_field_body) list

and struct_expr_body =
  | SEBident of module_path
  | SEBfunctor of mod_bound_id * module_type_body * struct_expr_body
  | SEBapply of struct_expr_body * struct_expr_body * constraints
  | SEBstruct of structure_body
  | SEBwith of struct_expr_body * with_declaration_body

and with_declaration_body =
    With_module_body of identifier list * module_path
  | With_definition_body of  identifier list * constant_body

and module_body =
    {  (** absolute path of the module *)
      mod_mp : module_path;
      (** Implementation *)
      mod_expr : struct_expr_body option; 
      (** Signature *)
      mod_type : struct_expr_body;
      (** algebraic structure expression is kept 
	 if it's relevant for extraction  *)
      mod_type_alg : struct_expr_body option; 
      (** set of all constraint in the module  *)
      mod_constraints : constraints;
      (** quotiented set of equivalent constant and inductive name  *)
      mod_delta : delta_resolver;
      mod_retroknowledge : Retroknowledge.action list}
      
and module_type_body =
    { 
      (** Path of the module type *)
      typ_mp : module_path;
      typ_expr : struct_expr_body;
      (** algebraic structure expression is kept 
	 if it's relevant for extraction  *)
      typ_expr_alg : struct_expr_body option ;
      typ_constraints : constraints;
      (** quotiented set of equivalent constant and inductive name  *)
      typ_delta :delta_resolver}
