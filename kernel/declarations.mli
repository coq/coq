(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Context

(** This module defines the internal representation of global
   declarations. This includes global constants/axioms, mutual
   inductive definitions, modules and module types *)

type engagement = ImpredicativeSet

(** {6 Representation of constants (Definition/Axiom) } *)

type polymorphic_arity = {
  poly_param_levels : Univ.universe option list;
  poly_level : Univ.universe;
}

type constant_type =
  | NonPolymorphicType of types
  | PolymorphicArity of rel_context * polymorphic_arity

(** Inlining level of parameters at functor applications.
    None means no inlining *)

type inline = int option

(** A constant can have no body (axiom/parameter), or a
    transparent body, or an opaque one *)

type constant_def =
  | Undef of inline
  | Def of Lazyconstr.constr_substituted
  | OpaqueDef of Lazyconstr.lazy_constr

type native_name =
  | Linked of string
  | LinkedLazy of string
  | LinkedInteractive of string
  | NotLinked

type constant_body = {
    const_hyps : Context.section_context; (** New: younger hyp at top *)
    const_body : constant_def;
    const_type : constant_type;
    const_body_code : Cemitcodes.to_patch_substituted;
    const_constraints : Univ.constraints;
    const_native_name : native_name ref;
    const_inline_code : bool }

(** {6 Representation of mutual inductive types in the kernel } *)

type recarg =
  | Norec
  | Mrec of inductive
  | Imbr of inductive

type wf_paths = recarg Rtree.t

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

    mind_typename : Id.t; (** Name of the type: [Ii] *)

    mind_arity_ctxt : rel_context; (** Arity context of [Ii] with parameters: [forall params, Ui] *)

    mind_arity : inductive_arity; (** Arity sort and original user arity if monomorphic *)

    mind_consnames : Id.t array; (** Names of the constructors: [cij] *)

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

    mind_hyps : Context.section_context;  (** Section hypotheses on which the block depends *)

    mind_nparams : int;  (** Number of expected parameters *)

    mind_nparams_rec : int;  (** Number of recursively uniform (i.e. ordinary) parameters *)

    mind_params_ctxt : rel_context;  (** The context of parameters (includes let-in declaration) *)

    mind_constraints : Univ.constraints;  (** Universes constraints enforced by the inductive declaration *)

(** {8 Data for native compilation } *)

    mind_native_name : native_name ref; (** status of the code (linked or not, and where) *)


  }

(** {6 Modules: signature component specifications, module types, and
  module declarations } *)

type structure_field_body =
  | SFBconst of constant_body
  | SFBmind of mutual_inductive_body
  | SFBmodule of module_body
  | SFBmodtype of module_type_body

(** NB: we may encounter now (at most) twice the same label in
    a [structure_body], once for a module ([SFBmodule] or [SFBmodtype])
    and once for an object ([SFBconst] or [SFBmind]) *)

and structure_body = (Label.t * structure_field_body) list

and struct_expr_body =
  | SEBident of module_path
  | SEBfunctor of MBId.t * module_type_body * struct_expr_body
  | SEBapply of struct_expr_body * struct_expr_body * Univ.constraints
  | SEBstruct of structure_body
  | SEBwith of struct_expr_body * with_declaration_body

and with_declaration_body =
    With_module_body of Id.t list * module_path
  | With_definition_body of  Id.t list * constant_body

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
      mod_constraints : Univ.constraints;
      (** quotiented set of equivalent constant and inductive name  *)
      mod_delta : Mod_subst.delta_resolver;
      mod_retroknowledge : Retroknowledge.action list}

and module_type_body =
    {
      (** Path of the module type *)
      typ_mp : module_path;
      typ_expr : struct_expr_body;
      (** algebraic structure expression is kept
	 if it's relevant for extraction  *)
      typ_expr_alg : struct_expr_body option ;
      typ_constraints : Univ.constraints;
      (** quotiented set of equivalent constant and inductive name  *)
      typ_delta : Mod_subst.delta_resolver}
