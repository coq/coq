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
  let t = Constrintern.intern_gen true ( !evdref) env t in
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
	| Anonymous -> Namegen.next_name_away (Namegen.named_hd env t' Anonymous) ids
	| Name id -> id
      in
      let d = (i,None,t') in
	(push_named d env, i :: ids, d::params))
    (env, avoid, []) l

let interp_constrs_evars isevars env avoid l =
  List.fold_left
    (fun (env, ids, params) t ->
      let t' = interp_binder_evars isevars env Anonymous t in
      let id = Namegen.next_name_away (Namegen.named_hd env t' Anonymous) ids in
      let d = (id,None,t') in
	(push_named d env, id :: ids, d::params))
    (env, avoid, []) l

let interp_constr_evars_gen evdref env ?(impls=([],[])) kind c =
  SPretyping.understand_tcc_evars evdref env kind
    (intern_gen (kind=IsType) ~impls ( !evdref) env c)

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

let new_instance ?(global=false) ctx (instid, bk, cl) props ?(generalize=true) pri =
  let env = Global.env() in
  let isevars = ref Evd.empty in
  let tclass, _ =
    match bk with
    | Implicit ->
	Implicit_quantifiers.implicit_application Idset.empty (* need no avoid *)
	  ~allow_partial:false (fun avoid (clname, (id, _, t)) ->
	    match clname with
	    | Some (cl, b) ->
		let t =
		  if b then
		    let _k = class_info cl in
		      CHole (Util.dummy_loc, Some Evd.InternalHole)
		  else CHole (Util.dummy_loc, None)
		in t, avoid
	    | None -> failwith ("new instance: under-applied typeclass"))
	  cl
      | Explicit -> cl, Idset.empty
  in
  let tclass = if generalize then CGeneralization (dummy_loc, Implicit, Some AbsPi, tclass) else tclass in
  let k, ctx', imps, subst =
    let c = Topconstr.prod_constr_expr tclass ctx in
    let c', imps = interp_type_evars_impls ~evdref:isevars env c in
    let ctx, c = decompose_prod_assum c' in
    let cl, args = Typeclasses.dest_class_app (push_rel_context ctx env) c in
      cl, ctx, imps, (List.rev args)
  in
  let id =
    match snd instid with
    | Name id ->
	let sp = Lib.make_path id in
	  if Nametab.exists_cci sp then
	    errorlabstrm "new_instance" (Nameops.pr_id id ++ Pp.str " already exists");
	  id
    | Anonymous ->
	let i = Nameops.add_suffix (Classes.id_of_class k) "_instance_0" in
	  Namegen.next_global_ident_away i (Termops.ids_of_context env)
  in
  let env' = push_rel_context ctx' env in
  isevars := Evarutil.nf_evar_defs !isevars;
  isevars := resolve_typeclasses ~onlyargs:false ~fail:true env' !isevars;
  let sigma =  !isevars in
  let subst = List.map (Evarutil.nf_evar sigma) subst in
  let subst =
    let props =
      match props with
      | CRecord (loc, _, fs) ->
	  if List.length fs > List.length k.cl_props then
	    Classes.mismatched_props env' (List.map snd fs) k.cl_props;
	  fs
      | _ ->
	  if List.length k.cl_props <> 1 then
	    errorlabstrm "new_instance" (Pp.str "Expected a definition for the instance body")
	  else [Ident (dummy_loc, Nameops.out_name (pi1 (List.hd k.cl_props))), props]
    in
      match k.cl_props with
      | [(na,b,ty)] ->
	  let term = match props with [] -> CHole (Util.dummy_loc, None) | [(_,f)] -> f | _ -> assert false in
	  let ty' = substl subst ty in
	  let c = interp_casted_constr_evars isevars env' term ty' in
	    c :: subst
      | _ ->
	  let get_id (idref, c) =
	    match idref with
	      | Ident id' -> id'
	      | _ ->
		  errorlabstrm "new_instance"
		    (Pp.str "only local structures are managed")
	  in
	  let props, rest =
	    List.fold_left
	      (fun (props, rest) (id,_,_) ->
		 try
		   let (loc_mid, c) =
		     List.find (fun elt -> Name (snd (get_id elt)) = id) rest
		   in
		   let rest' =
		     List.filter (fun elt -> Name (snd (get_id elt)) <> id) rest
		   in
		   match loc_mid with
		     | Ident (loc, mid) ->
			 Option.iter (fun x -> Dumpglob.add_glob loc (ConstRef x)) (List.assoc mid k.cl_projs);
			 c :: props, rest'
		     | _ -> errorlabstrm "new_instance"
			 (Pp.str "only local structures are managed")
		 with Not_found ->
		   (CHole (Util.dummy_loc, None) :: props), rest)
	      ([], props) k.cl_props
	  in
	    if rest <> [] then
	      unbound_method env' k.cl_impl (get_id (List.hd rest))
	    else
	      fst (type_ctx_instance isevars env' k.cl_props props subst)
  in
  let subst = List.fold_left2
    (fun subst' s (_, b, _) -> if b = None then s :: subst' else subst')
    [] subst (k.cl_props @ snd k.cl_context)
  in
  let inst_constr, ty_constr = instance_constructor k subst in
  isevars := Evarutil.nf_evar_defs !isevars;
  let term = Evarutil.nf_isevar !isevars (it_mkLambda_or_LetIn inst_constr ctx')
  and termtype = Evarutil.nf_isevar !isevars (it_mkProd_or_LetIn ty_constr ctx')
  in
    isevars := undefined_evars !isevars;
    Evarutil.check_evars env Evd.empty !isevars termtype;
    let hook vis gr =
      let cst = match gr with ConstRef kn -> kn | _ -> assert false in
      let inst = Typeclasses.new_instance k pri global (ConstRef cst) in
	Impargs.declare_manual_implicits false gr ~enriching:false imps;
	Typeclasses.add_instance inst
    in
    let evm = Subtac_utils.evars_of_term !isevars Evd.empty term in
    let obls, _, constr, typ = Eterm.eterm_obligations env id !isevars evm 0 term termtype in
      id, Subtac_obligations.add_definition id ~term:constr typ ~kind:(Global,false,Instance) ~hook obls
