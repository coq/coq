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
(*i*)

(* This module defines the types of global declarations. This includes
   global constants/axioms and mutual inductive definitions *)

(*s Constants (internal representation) (Definition/Axiom) *)

type subst_internal = 
  | Constr of constr 
  | LazyConstr of substitution * constr

type constr_substituted = subst_internal ref

let from_val c = ref (Constr c)

let force cs = match !cs with
    Constr c -> c
  | LazyConstr (subst,c) -> 
      let c' = subst_mps subst c in
	cs := Constr c';
	c'

let subst_constr_subst subst cs = match !cs with
    Constr c -> ref (LazyConstr (subst,c))
  | LazyConstr (subst',c) -> 
      let subst'' = join subst' subst in
	ref (LazyConstr (subst'',c))

type constant_body = {
  const_hyps : section_context; (* New: younger hyp at top *)
  const_body : constr_substituted option;
  const_type : types;
  const_constraints : constraints;
  const_opaque : bool }

(*s Inductive types (internal representation with redundant
    information). *)

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
  mind_equiv : kernel_name option
 }

(* TODO: should be changed to non-coping after Term.subst_mps *)
let subst_const_body sub cb = 
  { const_body = option_app (subst_constr_subst sub) cb.const_body;
    const_type = type_app (Term.subst_mps sub) cb.const_type;
    const_hyps = (assert (cb.const_hyps=[]); []);
    const_constraints = cb.const_constraints;
    const_opaque = cb.const_opaque}
  
let subst_mind_packet sub mbp = 
  { mind_consnames = mbp.mind_consnames;
    mind_typename = mbp.mind_typename;
    mind_nf_lc = 
      array_smartmap (type_app (Term.subst_mps sub)) mbp.mind_nf_lc;
    mind_nf_arity = type_app (Term.subst_mps sub) mbp.mind_nf_arity;
    mind_user_lc = 
      array_smartmap (type_app (Term.subst_mps sub)) mbp.mind_user_lc;
    mind_user_arity = type_app (Term.subst_mps sub) mbp.mind_user_arity;
    mind_sort = mbp.mind_sort;
    mind_nrealargs = mbp.mind_nrealargs;
    mind_kelim = mbp.mind_kelim;
    mind_nparams = mbp.mind_nparams;
    mind_params_ctxt = 
      map_rel_context (Term.subst_mps sub) mbp.mind_params_ctxt;
    mind_recargs = subst_wf_paths sub mbp.mind_recargs (*wf_paths*);
}

let subst_mind sub mib = 
  { mind_finite = mib.mind_finite ;
    mind_ntypes = mib.mind_ntypes ;
    mind_hyps = (assert (mib.mind_hyps=[]); []) ;
    mind_packets = array_smartmap (subst_mind_packet sub) mib.mind_packets ;
    mind_constraints = mib.mind_constraints ;
    mind_equiv = option_app (subst_kn sub) mib.mind_equiv;
}


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
  | MEBapply of module_expr_body * module_expr_body
      * constraints

and module_body = 
    { mod_expr : module_expr_body option;
      mod_user_type : module_type_body option;
      mod_type : module_type_body;
      mod_equiv : module_path option;
      mod_constraints : constraints }
