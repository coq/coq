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
open Sign
(*i*)

(* This module defines the internal representation of global
   declarations. This includes global constants/axioms, mutual
   inductive definitions, modules and module types *)

(*s Constants (Definition/Axiom) *)

type constr_substituted

val from_val : constr -> constr_substituted
val force : constr_substituted -> constr

type constant_body = {
  const_hyps : section_context; (* New: younger hyp at top *)
  const_body : constr_substituted option;
  const_type : types;
  const_constraints : constraints;
  const_opaque : bool }

val subst_const_body : substitution -> constant_body -> constant_body

(*s Inductive types (internal representation with redundant
    information). *)

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

(* [mind_typename] is the name of the inductive; [mind_arity] is
   the arity generalized over global parameters; [mind_lc] is the list
   of types of constructors generalized over global parameters and
   relative to the global context enriched with the arities of the
   inductives *) 

type one_inductive_body = {
  mind_typename : identifier;
  mind_nparams : int;
  mind_params_ctxt : rel_context;
  mind_nrealargs : int;
  mind_nf_arity : types;
  mind_user_arity : types;
  mind_sort : sorts;
  mind_kelim : sorts_family list;
  mind_consnames : identifier array;
  mind_nf_lc : types array; (* constrs and arity with pre-expanded ccl *)
  mind_user_lc : types array;
  mind_recargs : wf_paths;
 }

type mutual_inductive_body = {
  mind_finite : bool;
  mind_ntypes : int;
  mind_hyps : section_context;
  mind_packets : one_inductive_body array;
  mind_constraints : constraints;
  mind_equiv : kernel_name option;
 }


val subst_mind : substitution -> mutual_inductive_body -> mutual_inductive_body


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
    (*    type_of(equiv) <: modtype  (if given)  
       +  substyping of past With_Module mergers *)


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
      * constraints  (* type_of(A) <: input_type_of(F) *)

and module_body = 
    { mod_expr : module_expr_body option;
      mod_user_type : module_type_body option;
      mod_type : module_type_body;
      mod_equiv : module_path option;
      mod_constraints : constraints }
    (*    type_of(mod_expr)  <: mod_user_type (if given)  *)
    (*  if equiv given then constraints are empty *)



