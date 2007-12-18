(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: classes.mli 6748 2005-02-18 22:17:50Z herbelin $ i*)

open Pretyping
open Evd
open Environ
open Term
open Topconstr
open Names
open Libnames
open Pp
open Vernacexpr
open Constrintern
open Subtac_command
open Typeclasses
open Typeclasses_errors
open Termops
open Decl_kinds
open Entries

module SPretyping = Subtac_pretyping.Pretyping

let interp_binder_evars evdref env na t =
  let t = Constrintern.intern_gen true (Evd.evars_of !evdref) env t in
    SPretyping.understand_tcc_evars evdref env IsType t

let interp_binders_evars isevars env avoid l =
  List.fold_left
    (fun (env, ids, params) ((loc, i), t) -> 
      let n = Name i in
      let t' = interp_binder_evars isevars env n t in
      let d = (i,None,t') in
	(push_named d env, i :: ids, d::params))
    (env, avoid, []) l

let interp_typeclass_context_evars isevars env avoid l =
  List.fold_left
    (fun (env, ids, params) (iid, (loc, i), l) -> 
      let t' = interp_binder_evars isevars env (snd iid) (Implicit_quantifiers.constr_expr_of_constraint (loc,i) l) in
      let i = match snd iid with
	| Anonymous -> Nameops.next_name_away (Termops.named_hd env t' Anonymous) ids
	| Name id -> id
      in
      let d = (i,None,t') in
	(push_named d env, i :: ids, d::params))
    (env, avoid, []) l

let interp_constrs_evars isevars env avoid l =
  List.fold_left
    (fun (env, ids, params) t -> 
      let t' = interp_binder_evars isevars env Anonymous t in
      let id = Nameops.next_name_away (Termops.named_hd env t' Anonymous) ids in
      let d = (id,None,t') in
	(push_named d env, id :: ids, d::params))
    (env, avoid, []) l
    
let type_ctx_instance isevars env ctx inst subst =
  List.fold_left2
    (fun (subst, instctx) (na, _, t) ce ->
      let t' = replace_vars subst t in
      let c = interp_casted_constr_evars isevars env ce t' in
      let d = na, Some c, t' in
	(na, c) :: subst, d :: instctx)
    (subst, []) (List.rev ctx) inst

let substitution_of_constrs ctx cstrs =
  List.fold_right2 (fun c (na, _, _) acc -> (na, c) :: acc) cstrs ctx []

let new_instance sup  (instid, (bk, id), par) props =
  let env = Global.env() in
  let isevars = ref (Evd.create_evar_defs Evd.empty) in
  let avoid = Termops.ids_of_context env in
  let k = 
    try class_info (snd id)
    with Not_found -> unbound_class env id
  in
  let gen_ctx, sup = Implicit_quantifiers.resolve_class_binders env sup in
  let gen_ctx = 
    let is_free ((_, x), _) = 
      let f l = not (List.exists (fun ((_, y), _) -> y = x) l) in
      let g l = not (List.exists (fun ((_, y), _, _) -> y = Name x) l) in
	f gen_ctx && g sup
    in
    let parbinders = Implicit_quantifiers.compute_constrs_freevars_binders env par in
    let parbinders' = List.filter is_free parbinders in
      gen_ctx @ parbinders'
  in
  let env', avoid, genctx = interp_binders_evars isevars env avoid gen_ctx in
  let env', avoid, supctx = interp_typeclass_context_evars isevars env' avoid sup in

  let subst =
    match bk with
	Explicit ->
	  if List.length par <> List.length k.cl_context + List.length k.cl_params then 
	    Classes.mismatched_params env par (k.cl_params @ k.cl_context);
	  let len = List.length k.cl_context in
	  let ctx, par = Util.list_chop len par in
	  let subst, _ = type_ctx_instance isevars env' k.cl_context ctx [] in
	  let subst = Typeclasses.substitution_of_named_context isevars env' k.cl_name len subst 
	    k.cl_super
	  in
	  let subst, par = type_ctx_instance isevars env' k.cl_params par subst in subst

      | Implicit ->
	  let t' = interp_type_evars isevars env' (Topconstr.mkAppC (CRef (Ident id), par)) in
	    match kind_of_term t' with 
		App (c, args) -> 
		  substitution_of_constrs (k.cl_params @ k.cl_super @ k.cl_context) 
		    (List.rev (Array.to_list args))
	      | _ -> assert false
  in
  isevars := Evarutil.nf_evar_defs !isevars;
  let sigma = Evd.evars_of !isevars in
  let substctx = Typeclasses.nf_substitution sigma subst in
  let subst, _propsctx = 
    let props = 
      List.map (fun (x, l, d) -> 
	x, Topconstr.abstract_constr_expr d (Classes.binders_of_lidents l))
	props
    in
      if List.length props > List.length k.cl_props then 
	Classes.mismatched_props env' (List.map snd props) k.cl_props;
      let props, rest = 
	List.fold_left
	  (fun (props, rest) (id,_,_) -> 
	    try 
	      let (_, c) = List.find (fun ((_,id'), c) -> id' = id) rest in
	      let rest' = List.filter (fun ((_,id'), c) -> id' <> id) rest in
		c :: props, rest'
	    with Not_found -> (CHole Util.dummy_loc :: props), rest)
	  ([], props) k.cl_props
      in
	if rest <> [] then 
	  unbound_method env k.cl_name (fst (List.hd rest))
	else
	  type_ctx_instance isevars env' k.cl_props props substctx
  in
  let app = 
    applistc (mkConstruct (k.cl_impl, 1)) (List.rev_map snd subst)
  in 
  let term = it_mkNamedLambda_or_LetIn (it_mkNamedLambda_or_LetIn app supctx) genctx in
  isevars := Evarutil.nf_evar_defs !isevars;
  let term = Evarutil.nf_isevar !isevars term in
  let termtype = 
    let app = applistc (mkInd (k.cl_impl)) (List.rev_map snd substctx) in
    let t = it_mkNamedProd_or_LetIn (it_mkNamedProd_or_LetIn app supctx) genctx in
      Evarutil.nf_isevar !isevars t
  in
  isevars := undefined_evars !isevars;
  let id =
    match snd instid with
	Name id -> id
      | Anonymous -> 
	  let i = Nameops.add_suffix (snd id) "_instance_" in
	    Termops.next_global_ident_away false i (Termops.ids_of_context env)
  in
  let imps = 
    Util.list_map_i 
      (fun i (na, b, t) -> ExplByPos (i, Some na), (true, true))
      1 (genctx @ List.rev supctx)
  in
  let hook cst = 
    let inst = 
      { is_class = k;
	is_name = id;
(* 	is_params = paramsctx; *)
(* 	is_super = superctx; *)
	is_impl = cst;
(* 	is_add_hint = (fun () -> Classes.add_instance_hint id); *)
      }
    in
      Classes.add_instance_hint id;
      Impargs.declare_manual_implicits false (ConstRef cst) false imps;
      Typeclasses.add_instance inst
  in
  let evm = Subtac_utils.evars_of_term (Evd.evars_of !isevars) Evd.empty term in
  let obls, constr = Eterm.eterm_obligations env id !isevars evm 0 term (Some termtype) in
    ignore (Subtac_obligations.add_definition id constr termtype ~kind:Instance ~hook obls)
