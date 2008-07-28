(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Pretyping
open Evd
open Environ
open Term
open Rawterm
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
open Util

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
    (fun (env, ids, params) (iid, bk, cl) -> 
      let t' = interp_binder_evars isevars env (snd iid) cl in
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
    
let interp_constr_evars_gen evdref env ?(impls=([],[])) kind c =
  SPretyping.understand_tcc_evars evdref env kind
    (intern_gen (kind=IsType) ~impls (Evd.evars_of !evdref) env c)

let interp_casted_constr_evars evdref env ?(impls=([],[])) c typ =
  interp_constr_evars_gen evdref env ~impls (OfType (Some typ)) c

let type_ctx_instance isevars env ctx inst subst =
  List.fold_left2
    (fun (subst, instctx) (na, _, t) ce ->
      let t' = substl subst t in
      let c = interp_casted_constr_evars isevars env ce t' in
      isevars := resolve_typeclasses ~onlyargs:true ~fail:true env !isevars;
      let d = na, Some c, t' in
	c :: subst, d :: instctx)
    (subst, []) (List.rev ctx) inst

let type_class_instance_params isevars env id n ctx inst subst =
  List.fold_left2
    (fun (subst, instctx) (na, _, t) ce ->
      let t' = replace_vars subst t in
      let c = interp_casted_constr_evars isevars env ce t' in
      let d = na, Some c, t' in
	(na, c) :: subst, d :: instctx)
    (subst, []) (List.rev ctx) inst

let substitution_of_constrs ctx cstrs =
  List.fold_right2 (fun c (na, _, _) acc -> (na, c) :: acc) cstrs ctx []

let new_instance ?(global=false) ctx (instid, bk, cl) props ?(on_free_vars=Classes.default_on_free_vars) pri =
  let env = Global.env() in
  let isevars = ref (Evd.create_evar_defs Evd.empty) in
  let bound = Implicit_quantifiers.ids_of_list (Termops.ids_of_context env) in
  let bound, fvs = Implicit_quantifiers.free_vars_of_binders ~bound [] ctx in
  let tclass =
    match bk with
      | Implicit ->
	  let loc, id, par = Implicit_quantifiers.destClassAppExpl cl in
	  let k = class_info (Nametab.global id) in
	  let applen = List.fold_left (fun acc (x, y) -> if y = None then succ acc else acc) 0 par in
	  let needlen = List.fold_left (fun acc (x, y) -> if x = None then succ acc else acc) 0 k.cl_context in
	    if needlen <> applen then 
	      Classes.mismatched_params env (List.map fst par) (List.map snd k.cl_context);
	    let pars, _ = Implicit_quantifiers.combine_params Idset.empty (* need no avoid *)
	      (fun avoid (clname, (id, _, t)) -> 
		match clname with 
		    Some (cl, b) -> 
		      let t = 
			if b then 
			  let _k = class_info cl in
			    CHole (Util.dummy_loc, Some Evd.InternalHole) (* (Evd.ImplicitArg (IndRef k.cl_impl, (1, None)))) *)
			else CHole (Util.dummy_loc, None)
		      in t, avoid
		  | None -> failwith ("new instance: under-applied typeclass"))
	      par (List.rev k.cl_context)
	    in Topconstr.CAppExpl (loc, (None, id), pars)

      | Explicit -> cl
  in
  let ctx_bound = Idset.union bound (Implicit_quantifiers.ids_of_list fvs) in
  let gen_ids = Implicit_quantifiers.free_vars_of_constr_expr ~bound:ctx_bound tclass [] in
  let bound = Idset.union (Implicit_quantifiers.ids_of_list gen_ids) ctx_bound in
  on_free_vars (List.rev (gen_ids @ fvs));
  let gen_ctx = Implicit_quantifiers.binder_list_of_ids gen_ids in
  let ctx, avoid = Classes.name_typeclass_binders bound ctx in
  let ctx = List.append ctx (List.rev gen_ctx) in
  let k, ctx', imps, subst = 
    let c = Command.generalize_constr_expr tclass ctx in
    let c', imps = interp_type_evars_impls ~evdref:isevars env c in
    let ctx, c = Sign.decompose_prod_assum c' in
    let cl, args = Typeclasses.dest_class_app c in
      cl, ctx, imps, (List.rev (Array.to_list args))
  in
  let id = 
    match snd instid with
	Name id -> 
	  let sp = Lib.make_path id in
	    if Nametab.exists_cci sp then
	      errorlabstrm "new_instance" (Nameops.pr_id id ++ Pp.str " already exists");
	    id
      | Anonymous -> 
	  let i = Nameops.add_suffix (Classes.id_of_class k) "_instance_0" in
	    Termops.next_global_ident_away false i (Termops.ids_of_context env)
  in
  let env' = push_rel_context ctx' env in
  isevars := Evarutil.nf_evar_defs !isevars;
  isevars := resolve_typeclasses ~onlyargs:false ~fail:true env' !isevars;
  let sigma = Evd.evars_of !isevars in
  let substctx = List.map (Evarutil.nf_evar sigma) subst in
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
	      let ((loc, mid), c) = List.find (fun ((_,id'), c) -> Name id' = id) rest in
	      let rest' = List.filter (fun ((_,id'), c) -> Name id' <> id) rest in
		Constrintern.add_glob loc (ConstRef (List.assoc mid k.cl_projs));
		c :: props, rest'
	    with Not_found -> (CHole (Util.dummy_loc, None) :: props), rest)
	  ([], props) k.cl_props
      in
	if rest <> [] then 
	  unbound_method env' k.cl_impl (fst (List.hd rest))
	else
	  type_ctx_instance isevars env' k.cl_props props substctx
  in
  let inst_constr, ty_constr = instance_constructor k (List.rev subst) in
    isevars := Evarutil.nf_evar_defs !isevars;
    let term = Evarutil.nf_isevar !isevars (it_mkLambda_or_LetIn inst_constr ctx')
    and termtype = Evarutil.nf_isevar !isevars (it_mkProd_or_LetIn ty_constr ctx') 
    in
      isevars := undefined_evars !isevars;
      Evarutil.check_evars env Evd.empty !isevars termtype;
      let hook gr = 
	let cst = match gr with ConstRef kn -> kn | _ -> assert false in
	let inst = Typeclasses.new_instance k pri global cst in
	  Impargs.declare_manual_implicits false gr false imps;
	  Typeclasses.add_instance inst
      in
      let evm = Subtac_utils.evars_of_term (Evd.evars_of !isevars) Evd.empty term in
      let obls, constr, typ = Eterm.eterm_obligations env id !isevars evm 0 term termtype in
	ignore(Subtac_obligations.add_definition id constr typ ~kind:(Global,false,Instance) ~hook obls);
	id
