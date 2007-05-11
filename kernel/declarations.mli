(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Univ
open Term
open Cemitcodes
open Sign
open Mod_subst
(*i*)

(* This module defines the internal representation of global
   declarations. This includes global constants/axioms, mutual
   inductive definitions, modules and module types *)

type engagement = ImpredicativeSet

(**********************************************************************)
(*s Representation of constants (Definition/Axiom)                    *)

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
    const_hyps : section_context; (* New: younger hyp at top *)
    const_body : constr_substituted option;
    const_type : constant_type;
    const_body_code : to_patch_substituted;
   (*i const_type_code : to_patch;i*)
    const_constraints : constraints;
    const_opaque : bool;
    const_inline : bool}

val subst_const_body : substitution -> constant_body -> constant_body

(**********************************************************************)
(*s Representation of mutual inductive types in the kernel            *)

type recarg = 
  | Norec 
  | Mrec of int 
  | Imbr of inductive

val subst_recarg : substitution -> recarg -> recarg

type wf_paths = recarg Rtree.t

val mk_norec : wf_paths
val mk_paths : recarg -> wf_paths list array -> wf_paths
val dest_recarg : wf_paths -> recarg
val dest_subterms : wf_paths -> wf_paths list array
val recarg_length : wf_paths -> int -> int

val subst_wf_paths : substitution -> wf_paths -> wf_paths

(*
\begin{verbatim}
   Inductive I1 (params) : U1 := c11 : T11 | ... | c1p1 : T1p1
   ...
   with      In (params) : Un := cn1 : Tn1 | ... | cnpn : Tnpn
\end{verbatim}
*)

type monomorphic_inductive_arity = {
  mind_user_arity : constr;
  mind_sort : sorts;
}

type inductive_arity = 
| Monomorphic of monomorphic_inductive_arity
| Polymorphic of polymorphic_arity

type one_inductive_body = {

(* Primitive datas *)

 (* Name of the type: [Ii] *)
    mind_typename : identifier;

 (* Arity context of [Ii] with parameters: [forall params, Ui] *)
    mind_arity_ctxt : rel_context;

 (* Arity sort and original user arity if monomorphic *)
    mind_arity : inductive_arity;

 (* Names of the constructors: [cij] *)
    mind_consnames : identifier array;

 (* Types of the constructors with parameters: [forall params, Tij],
    where the Ik are replaced by de Bruijn index in the context
    I1:forall params, U1 ..  In:forall params, Un *)
    mind_user_lc : types array;

(* Derived datas *)

 (* Number of expected real arguments of the type (no let, no params) *)
    mind_nrealargs : int;

 (* List of allowed elimination sorts *)
    mind_kelim : sorts_family list;

 (* Head normalized constructor types so that their conclusion is atomic *)
    mind_nf_lc : types array;

 (* Length of the signature of the constructors (with let, w/o params) *)
    mind_consnrealdecls : int array;

 (* Signature of recursive arguments in the constructors *)
    mind_recargs : wf_paths;

(* Datas for bytecode compilation *)

 (* number of constant constructor *)
    mind_nb_constant : int;

 (* number of no constant constructor *)
    mind_nb_args : int;

    mind_reloc_tbl :  Cbytecodes.reloc_table; 
  }

type mutual_inductive_body = {

  (* The component of the mutual inductive block *)
    mind_packets : one_inductive_body array;

  (* Whether the inductive type has been declared as a record *)
    mind_record : bool;

  (* Whether the type is inductive or coinductive *)
    mind_finite : bool;

  (* Number of types in the block *)
    mind_ntypes : int;

  (* Section hypotheses on which the block depends *)
    mind_hyps : section_context;

  (* Number of expected parameters *)
    mind_nparams : int;

  (* Number of recursively uniform (i.e. ordinary) parameters *)
    mind_nparams_rec : int;

  (* The context of parameters (includes let-in declaration) *)
    mind_params_ctxt : rel_context;

  (* Universes constraints enforced by the inductive declaration *)
    mind_constraints : constraints;

  (* Source of the inductive block when aliased in a module *)
    mind_equiv : kernel_name option
  }

val subst_mind : substitution -> mutual_inductive_body -> mutual_inductive_body

(**********************************************************************)
(*s Modules: signature component specifications, module types, and
  module declarations *)

type specification_body = 
  | SPBconst of constant_body
  | SPBmind of mutual_inductive_body
  | SPBmodule of module_specification_body
  | SPBmodtype of module_type_body

and module_signature_body = (label * specification_body) list

and module_type_body = 
  | MTBident of kernel_name
  | MTBfunsig of mod_bound_id * module_type_body * module_type_body
  | MTBsig of mod_self_id * module_signature_body

and module_specification_body = 
    { msb_modtype : module_type_body;
      msb_equiv : module_path option; 
      msb_constraints : constraints }
    (*    [type_of](equiv) <: modtype  (if given)  
       +  substyping of past [With_Module] mergers *)


type structure_elem_body = 
  | SEBconst of constant_body
  | SEBmind of mutual_inductive_body
  | SEBmodule of module_body
  | SEBmodtype of module_type_body

and module_structure_body = (label * structure_elem_body) list

and module_expr_body =
  | MEBident of module_path
  | MEBfunctor of mod_bound_id * module_type_body * module_expr_body 
  | MEBstruct of mod_self_id * module_structure_body
  | MEBapply of module_expr_body * module_expr_body  (* (F A) *)
      * constraints  (* [type_of](A) <: [input_type_of](F) *)

and module_body = 
    { mod_expr : module_expr_body option;
      mod_user_type : module_type_body option;
      mod_type : module_type_body;
      mod_equiv : module_path option;
      mod_constraints : constraints;
      mod_retroknowledge : Retroknowledge.action list}
    (*    [type_of(mod_expr)]  <: [mod_user_type] (if given)  *)
    (*  if equiv given then constraints are empty *)



