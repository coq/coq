(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
open Decl_kinds
open Entries
open Util

module SPretyping = Subtac_pretyping.Pretyping

let interp_constr_evars_gen evdref env ?(impls=[]) kind c =
  SPretyping.understand_tcc_evars evdref env kind
    (intern_gen (kind=IsType) ~impls !evdref env c)

let interp_casted_constr_evars evdref env ?(impls=[]) c typ =
  interp_constr_evars_gen evdref env ~impls (OfType (Some typ)) c

let interp_context_evars evdref env params =
  Constrintern.interp_context_gen
    (fun env t -> SPretyping.understand_tcc_evars evdref env IsType t)
    (SPretyping.understand_judgment_tcc evdref) !evdref env params

let type_ctx_instance evars env ctx inst subst =
  let rec aux (subst, instctx) l = function
    (na, b, t) :: ctx ->
      let t' = substl subst t in
      let c', l =
	match b with
	| None -> interp_casted_constr_evars evars env (List.hd l) t', List.tl l
	| Some b -> substl subst b, l
      in
       evars := resolve_typeclasses ~onlyargs:true ~fail:true env !evars;
       let d = na, Some c', t' in
	aux (c' :: subst, d :: instctx) l ctx
    | [] -> subst
  in aux (subst, []) inst (List.rev ctx)

let new_instance ?(global=false) ctx (instid, bk, cl) props ?(generalize=true) pri =
  let env = Global.env() in
  let evars = ref Evd.empty in
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
  let k, cty, ctx', ctx, len, imps, subst =
    let (env', ctx), imps = interp_context_evars evars env ctx in
    let c', imps' = interp_type_evars_impls ~evdref:evars env' tclass in
    let len = List.length ctx in
    let imps = imps @ Impargs.lift_implicits len imps' in
    let ctx', c = decompose_prod_assum c' in
    let ctx'' = ctx' @ ctx in
    let cl, args = Typeclasses.dest_class_app (push_rel_context ctx'' env) c in
    let _, args = 
      List.fold_right (fun (na, b, t) (args, args') ->
	match b with
	| None -> (List.tl args, List.hd args :: args')
	| Some b -> (args, substl args' b :: args'))
	(snd cl.cl_context) (args, [])
    in
      cl, c', ctx', ctx, len, imps, args
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
  let env' = push_rel_context ctx env in
  evars := Evarutil.nf_evar_map !evars;
  evars := resolve_typeclasses ~onlyargs:false ~fail:true env !evars;
  let sigma =  !evars in
  let subst = List.map (Evarutil.nf_evar sigma) subst in
  let props =
    match props with
    | CRecord (loc, _, fs) ->
	if List.length fs > List.length k.cl_props then
	  Classes.mismatched_props env' (List.map snd fs) k.cl_props;
	Inl fs
    | _ -> Inr props
  in
  let subst =
    match props with
    | Inr term ->
	let c = interp_casted_constr_evars evars env' term cty in
	  Inr c
    | Inl props ->
	let get_id =
	  function
	    | Ident id' -> id'
	    | _ -> errorlabstrm "new_instance" (Pp.str "Only local structures are handled")
	in
	let props, rest =
	  List.fold_left
	    (fun (props, rest) (id,b,_) ->
	      if b = None then
		try
		  let (loc_mid, c) = List.find (fun (id', _) -> Name (snd (get_id id')) = id) rest in
		  let rest' = List.filter (fun (id', _) -> Name (snd (get_id id')) <> id) rest in
		  let (loc, mid) = get_id loc_mid in
		    Option.iter (fun x -> Dumpglob.add_glob loc (ConstRef x)) 
		      (List.assoc (Name mid) k.cl_projs);
		    c :: props, rest'
		with Not_found ->
		  (CHole (Util.dummy_loc, None) :: props), rest
	      else props, rest)
	    ([], props) k.cl_props
	in
	  if rest <> [] then
	    unbound_method env' k.cl_impl (get_id (fst (List.hd rest)))
	  else
	    Inl (type_ctx_instance evars (push_rel_context ctx' env') k.cl_props props subst)
  in	  
  evars := Evarutil.nf_evar_map !evars;
  let term, termtype =
    match subst with
    | Inl subst ->
	let subst = List.fold_left2
	  (fun subst' s (_, b, _) -> if b = None then s :: subst' else subst')
	  [] subst (k.cl_props @ snd k.cl_context)
	in
	let app, ty_constr = instance_constructor k subst in
	let termtype = it_mkProd_or_LetIn ty_constr (ctx' @ ctx) in
	let term = Termops.it_mkLambda_or_LetIn app (ctx' @ ctx) in
	  term, termtype
    | Inr def ->
	let termtype = it_mkProd_or_LetIn cty ctx in
	let term = Termops.it_mkLambda_or_LetIn def ctx in
	  term, termtype
  in
  let termtype = Evarutil.nf_evar !evars termtype in
  let term = Evarutil.nf_evar !evars term in
  evars := undefined_evars !evars;
  Evarutil.check_evars env Evd.empty !evars termtype;
  let hook vis gr =
    let cst = match gr with ConstRef kn -> kn | _ -> assert false in
    let inst = Typeclasses.new_instance k pri global (ConstRef cst) in
      Impargs.declare_manual_implicits false gr ~enriching:false [imps];
      Typeclasses.add_instance inst
  in
  let evm = Subtac_utils.evars_of_term !evars Evd.empty term in
  let obls, _, constr, typ = Eterm.eterm_obligations env id !evars evm 0 term termtype in
    id, Subtac_obligations.add_definition id ~term:constr typ ~kind:(Global,false,Instance) ~hook obls
