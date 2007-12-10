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

let interp_constrs_evars isevars env avoid l =
  List.fold_left
    (fun (env, ids, params) t -> 
      let t' = interp_binder_evars isevars env Anonymous t in
      let id = Nameops.next_name_away (Termops.named_hd env t' Anonymous) ids in
      let d = (id,None,t') in
	(push_named d env, id :: ids, d::params))
    (env, avoid, []) l

let new_instance instid id par sup props =
  let env = Global.env() in
  let isevars = ref (Evd.create_evar_defs Evd.empty) in
  let avoid = Termops.ids_of_context env in
  let k = 
    try class_info (snd id)
    with Not_found -> unbound_class env id
  in
  let gen_ctx = Implicit_quantifiers.compute_constrs_freevars_binders env (sup @ par) in
  let type_ctx_instance env ctx inst previnst =
    List.fold_left2
      (fun (inst, instctx, env) (na, _, t) ce -> 
	let c = interp_casted_constr_evars isevars env ce t in
	let d = na, Some c, t in
	let instc = substl inst c in
	  instc :: inst, d :: instctx, push_named d env)
      (previnst, [], env) (List.rev ctx) inst
  in
  let env', avoid, genctx = interp_binders_evars isevars env avoid gen_ctx in
  let env', avoid, supctx = interp_constrs_evars isevars env' avoid sup in
  let params, paramsctx, envctx = 
    if List.length par <> List.length k.cl_params then 
      Classes.mismatched_params env par k.cl_params;
    type_ctx_instance env' k.cl_params par []
  in
  let super, superctx =
    Classes.infer_super_instances envctx params paramsctx k.cl_super
  in
  let props, _, propsctx, env' = 
    let props = 
      List.map (fun (x, l, d) -> 
	x, Topconstr.abstract_constr_expr d (Classes.binders_of_lidents l))
	props
    in
      if List.length props > List.length k.cl_props then 
	Classes.mismatched_props env' (List.map snd props) k.cl_props;
      let props = 
	List.rev_map 
	  (fun (id,_,_) -> 
	    try 
	      let (_, c) = List.find (fun ((_,id'), c) -> id' = id) props in c
	    with Not_found -> CHole Util.dummy_loc)
	  k.cl_props
      in
      let type_defs_instance env ctx inst previnst subst =
	List.fold_left2
	  (fun (inst, ids, instctx, env) (na, _, t) ce -> 
	    let t' = replace_vars subst t in
	    let c = interp_casted_constr_evars isevars env ce t' in
	    let d = na, Some c, t' in
	    let instc = substl inst (subst_vars ids c) in
	      instc :: inst, na :: ids, d :: instctx, push_named d env)
	  (previnst, [], [], env) (List.rev ctx) inst
      in
      let subst = List.map (function (na, Some c, t) -> na, c | _ -> assert false) (superctx @ paramsctx) in 
	type_defs_instance env' k.cl_props props (super @ params) subst
  in
  let app = 
    applistc (mkConstruct (k.cl_impl, 1)) (List.rev props)
  in 
  let term = it_mkNamedLambda_or_LetIn (it_mkNamedLambda_or_LetIn app supctx) genctx in
  isevars := Evarutil.nf_evar_defs !isevars;
  let term = Evarutil.nf_isevar !isevars term in
  let termtype = 
    let app = applistc (mkInd (k.cl_impl)) (List.rev params @ List.rev super) in
    let t = it_mkNamedProd_or_LetIn (it_mkNamedProd_or_LetIn app supctx) genctx in
      Evarutil.nf_isevar !isevars t
  in
  isevars := undefined_evars !isevars;
  let id =
    match instid with
	Some (_, id) -> id
      | None -> 
	  let i = Nameops.add_suffix (snd id) "_instance_" in
	    Termops.next_global_ident_away false i (Termops.ids_of_context env)
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
      Typeclasses.add_instance inst
  in
  let evm = Subtac_utils.evars_of_term (Evd.evars_of !isevars) Evd.empty term in
  let obls, constr = Eterm.eterm_obligations env id !isevars evm 0 term (Some termtype) in
    ignore (Subtac_obligations.add_definition id constr termtype ~kind:Instance ~hook obls)
