(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Univ
open Term
open Sign
open Mod_subst
(*i*)

(* This module defines the types of global declarations. This includes
   global constants/axioms and mutual inductive definitions *)

type engagement = ImpredicativeSet


(*s Constants (internal representation) (Definition/Axiom) *)

type polymorphic_arity = {
  poly_param_levels : universe option list;
  poly_level : universe;
}

type constant_type =
  | NonPolymorphicType of types
  | PolymorphicArity of rel_context * polymorphic_arity

type constr_substituted = constr substituted

let from_val = from_val

let force = force subst_mps 

let subst_constr_subst = subst_substituted

type constant_body = {
    const_hyps : section_context; (* New: younger hyp at top *)
    const_body : constr_substituted option;
    const_type : constant_type;
    const_body_code : Cemitcodes.to_patch_substituted;
   (* const_type_code : Cemitcodes.to_patch; *)
    const_constraints : constraints;
    const_opaque : bool; 
    const_inline : bool}

(*s Inductive types (internal representation with redundant
    information). *)

let subst_rel_declaration sub (id,copt,t as x) =
  let copt' = Option.smartmap (subst_mps sub) copt in
  let t' = subst_mps sub t in
  if copt == copt' & t == t' then x else (id,copt',t')

let subst_rel_context sub = list_smartmap (subst_rel_declaration sub)

type recarg = 
  | Norec 
  | Mrec of int 
  | Imbr of inductive

let subst_recarg sub r = match r with
  | Norec | Mrec _  -> r
  | Imbr (kn,i) -> let kn' = subst_kn sub kn in
      if kn==kn' then r else Imbr (kn',i)

type wf_paths = recarg Rtree.t

let mk_norec = Rtree.mk_node Norec [||]

let mk_paths r recargs =
  Rtree.mk_node r
    (Array.map (fun l -> Rtree.mk_node Norec (Array.of_list l)) recargs)

let dest_recarg p = fst (Rtree.dest_node p)

let dest_subterms p =
  let (_,cstrs) = Rtree.dest_node p in
  Array.map (fun t -> Array.to_list (snd (Rtree.dest_node t))) cstrs

let recarg_length p j = 
  let (_,cstrs) = Rtree.dest_node p in
  Array.length (snd (Rtree.dest_node cstrs.(j-1)))

let subst_wf_paths sub p = Rtree.smartmap (subst_recarg sub) p

(**********************************************************************)
(* Representation of mutual inductive types in the kernel             *)
(*
   Inductive I1 (params) : U1 := c11 : T11 | ... | c1p1 : T1p1
   ...
   with      In (params) : Un := cn1 : Tn1 | ... | cnpn : Tnpn
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

 (* Arity sort, original user arity, and allowed elim sorts, if monomorphic *)
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

let subst_arity sub = function
| NonPolymorphicType s -> NonPolymorphicType (subst_mps sub s)
| PolymorphicArity (ctx,s) -> PolymorphicArity (subst_rel_context sub ctx,s)

(* TODO: should be changed to non-coping after Term.subst_mps *)
let subst_const_body sub cb = {
    const_hyps = (assert (cb.const_hyps=[]); []);
    const_body = Option.map (subst_constr_subst sub) cb.const_body;
    const_type = subst_arity sub cb.const_type;
    const_body_code = Cemitcodes.subst_to_patch_subst sub cb.const_body_code;
    (*const_type_code = Cemitcodes.subst_to_patch sub cb.const_type_code;*)
    const_constraints = cb.const_constraints;
    const_opaque = cb.const_opaque;
    const_inline = cb.const_inline} 

let subst_arity sub = function
| Monomorphic s ->
    Monomorphic {
      mind_user_arity = subst_mps sub s.mind_user_arity;
      mind_sort = s.mind_sort;
    }
| Polymorphic s as x -> x

let subst_mind_packet sub mbp = 
  { mind_consnames = mbp.mind_consnames;
    mind_consnrealdecls = mbp.mind_consnrealdecls;
    mind_typename = mbp.mind_typename;
    mind_nf_lc = array_smartmap (subst_mps sub) mbp.mind_nf_lc;
    mind_arity_ctxt = subst_rel_context sub mbp.mind_arity_ctxt;
    mind_arity = subst_arity sub mbp.mind_arity;
    mind_user_lc = array_smartmap (subst_mps sub) mbp.mind_user_lc;
    mind_nrealargs = mbp.mind_nrealargs;
    mind_kelim = mbp.mind_kelim;
    mind_recargs = subst_wf_paths sub mbp.mind_recargs (*wf_paths*); 
    mind_nb_constant = mbp.mind_nb_constant;
    mind_nb_args = mbp.mind_nb_args;
    mind_reloc_tbl = mbp.mind_reloc_tbl }


let subst_mind sub mib = 
  { mind_record = mib.mind_record ; 
    mind_finite = mib.mind_finite ;
    mind_ntypes = mib.mind_ntypes ;
    mind_hyps = (assert (mib.mind_hyps=[]); []) ;
    mind_nparams = mib.mind_nparams;
    mind_nparams_rec = mib.mind_nparams_rec;
    mind_params_ctxt = 
      map_rel_context (subst_mps sub) mib.mind_params_ctxt;
    mind_packets = array_smartmap (subst_mind_packet sub) mib.mind_packets ;
    mind_constraints = mib.mind_constraints ;
    mind_equiv = Option.map (subst_kn sub) mib.mind_equiv }


(*s Modules: signature component specifications, module types, and
  module declarations *)

type structure_field_body = 
  | SFBconst of constant_body
  | SFBmind of mutual_inductive_body
  | SFBmodule of module_body
  | SFBalias of module_path * struct_expr_body option 
      * constraints option
  | SFBmodtype of module_type_body

and structure_body = (label * structure_field_body) list

and struct_expr_body =
  | SEBident of module_path
  | SEBfunctor of mod_bound_id * module_type_body * struct_expr_body 
  | SEBstruct of mod_self_id * structure_body
  | SEBapply of struct_expr_body * struct_expr_body
      * constraints
  | SEBwith of struct_expr_body * with_declaration_body

and with_declaration_body =
    With_module_body of identifier list * module_path 
      * struct_expr_body option  * constraints
  | With_definition_body of  identifier list * constant_body
        
and module_body = 
    { mod_expr : struct_expr_body option;
      mod_type : struct_expr_body option;
      mod_constraints : constraints;
      mod_alias : substitution;
      mod_retroknowledge : Retroknowledge.action list}

and module_type_body = 
    { typ_expr : struct_expr_body;
      typ_strength : module_path option;
      typ_alias : substitution}
