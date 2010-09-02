(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Libnames
open Nameops
open Term
open Termops
open Environ
open Declarations
open Entries
open Declare
open Nametab
open Constrintern
open Command
open Inductive
open Safe_typing
open Decl_kinds
open Indtypes
open Type_errors
open Topconstr

(********** definition d'un record (structure) **************)

let interp_evars evdref env impls k typ =
  let typ' = intern_gen true ~impls !evdref env typ in
  let imps = Implicit_quantifiers.implicits_of_rawterm typ' in
    imps, Pretyping.Default.understand_tcc_evars evdref env k typ'

let interp_fields_evars evars env nots l =
  List.fold_left2
    (fun (env, uimpls, params, impls) no ((loc, i), b, t) ->
      let impl, t' = interp_evars evars env impls Pretyping.IsType t in
      let b' = Option.map (fun x -> snd (interp_evars evars env impls (Pretyping.OfType (Some t')) x)) b in
      let impls =
	match i with
	| Anonymous -> impls
	| Name id -> (id, compute_internalization_data env Constrintern.Method t' impl) :: impls
      in
      let d = (i,b',t') in
      List.iter (Metasyntax.set_notation_for_interpretation impls) no;
      (push_rel d env, impl :: uimpls, d::params, impls))
    (env, [], [], []) nots l

let binder_of_decl = function
  | Vernacexpr.AssumExpr(n,t) -> (n,None,t)
  | Vernacexpr.DefExpr(n,c,t) -> (n,Some c, match t with Some c -> c | None -> CHole (fst n, None))

let binders_of_decls = List.map binder_of_decl

let typecheck_params_and_fields id t ps nots fs =
  let env0 = Global.env () in
  let evars = ref Evd.empty in
  let (env1,newps), imps = interp_context_evars evars env0 ps in
  let fullarity = it_mkProd_or_LetIn (Option.cata (fun x -> x) (new_Type ()) t) newps in
  let env_ar = push_rel_context newps (push_rel (Name id,None,fullarity) env0) in
  let env2,impls,newfs,data =
    interp_fields_evars evars env_ar nots (binders_of_decls fs)
  in
  let evars = Evarconv.consider_remaining_unif_problems env_ar !evars in
  let evars = Typeclasses.resolve_typeclasses env_ar evars in
  let sigma =  evars in
  let newps = Evarutil.nf_rel_context_evar sigma newps in
  let newfs = Evarutil.nf_rel_context_evar sigma newfs in
  let ce t = Evarutil.check_evars env0 Evd.empty evars t in
    List.iter (fun (n, b, t) -> Option.iter ce b; ce t) newps;
    List.iter (fun (n, b, t) -> Option.iter ce b; ce t) newfs;
    imps, newps, impls, newfs

let degenerate_decl (na,b,t) =
  let id = match na with
    | Name id -> id
    | Anonymous -> anomaly "Unnamed record variable" in
  match b with
    | None -> (id, Entries.LocalAssum t)
    | Some b -> (id, Entries.LocalDef b)

type record_error =
  | MissingProj of identifier * identifier list
  | BadTypedProj of identifier * env * Type_errors.type_error

let warning_or_error coe indsp err =
  let st = match err with
    | MissingProj (fi,projs) ->
	let s,have = if List.length projs > 1 then "s","were" else "","was" in
        (str(string_of_id fi) ++
	   strbrk" cannot be defined because the projection" ++ str s ++ spc () ++
           prlist_with_sep pr_comma pr_id projs ++ spc () ++ str have ++
	   strbrk " not defined.")
    | BadTypedProj (fi,ctx,te) ->
	match te with
	  | ElimArity (_,_,_,_,Some (_,_,NonInformativeToInformative)) ->
              (pr_id fi ++
		strbrk" cannot be defined because it is informative and " ++
		Printer.pr_inductive (Global.env()) indsp ++
		strbrk " is not.")
	  | ElimArity (_,_,_,_,Some (_,_,StrongEliminationOnNonSmallType)) ->
	      (pr_id fi ++
		strbrk" cannot be defined because it is large and " ++
		Printer.pr_inductive (Global.env()) indsp ++
		strbrk " is not.")
	  | _ ->
              (pr_id fi ++ strbrk " cannot be defined because it is not typable.")
  in
  if coe then errorlabstrm "structure" st;
  Flags.if_verbose ppnl (hov 0 (str"Warning: " ++ st))

type field_status =
  | NoProjection of name
  | Projection of constr

exception NotDefinable of record_error

(* This replaces previous projection bodies in current projection *)
(* Undefined projs are collected and, at least one undefined proj occurs *)
(* in the body of current projection then the latter can not be defined *)
(* [c] is defined in ctxt [[params;fields]] and [l] is an instance of *)
(* [[fields]] defined in ctxt [[params;x:ind]] *)
let subst_projection fid l c =
  let lv = List.length l in
  let bad_projs = ref [] in
  let rec substrec depth c = match kind_of_term c with
    | Rel k ->
	(* We are in context [[params;fields;x:ind;...depth...]] *)
        if k <= depth+1 then
	  c
        else if k-depth-1 <= lv then
	  match List.nth l (k-depth-2) with
	    | Projection t -> lift depth t
	    | NoProjection (Name id) -> bad_projs := id :: !bad_projs; mkRel k
	    | NoProjection Anonymous -> assert false
        else
	  mkRel (k-lv)
    | _ -> map_constr_with_binders succ substrec depth c
  in
  let c' = lift 1 c in (* to get [c] defined in ctxt [[params;fields;x:ind]] *)
  let c'' = substrec 0 c' in
  if !bad_projs <> [] then
    raise (NotDefinable (MissingProj (fid,List.rev !bad_projs)));
  c''

let instantiate_possibly_recursive_type indsp paramdecls fields =
  let subst = list_map_i (fun i _ -> mkRel i) 1 paramdecls in
  substl_rel_context (subst@[mkInd indsp]) fields

(* We build projections *)
let declare_projections indsp ?(kind=StructureComponent) ?name coers fieldimpls fields =
  let env = Global.env() in
  let (mib,mip) = Global.lookup_inductive indsp in
  let paramdecls = mib.mind_params_ctxt in
  let r = mkInd indsp in
  let rp = applist (r, extended_rel_list 0 paramdecls) in
  let paramargs = extended_rel_list 1 paramdecls in (*def in [[params;x:rp]]*)
  let x = match name with Some n -> Name n | None -> Namegen.named_hd (Global.env()) r Anonymous in
  let fields = instantiate_possibly_recursive_type indsp paramdecls fields in
  let lifted_fields = lift_rel_context 1 fields in
  let (_,kinds,sp_projs,_) =
    list_fold_left3
      (fun (nfi,kinds,sp_projs,subst) coe (fi,optci,ti) impls ->
	let (sp_projs,subst) =
	  match fi with
	  | Anonymous ->
	      (None::sp_projs,NoProjection fi::subst)
	  | Name fid ->
            try
              let ccl = subst_projection fid subst ti in
	      let body = match optci with
              | Some ci -> subst_projection fid subst ci
              | None ->
	        (* [ccl] is defined in context [params;x:rp] *)
		(* [ccl'] is defined in context [params;x:rp;x:rp] *)
		let ccl' = liftn 1 2 ccl in
		let p = mkLambda (x, lift 1 rp, ccl') in
		let branch = it_mkLambda_or_LetIn (mkRel nfi) lifted_fields in
		let ci = Inductiveops.make_case_info env indsp LetStyle in
		mkCase (ci, p, mkRel 1, [|branch|]) in
	      let proj =
	        it_mkLambda_or_LetIn (mkLambda (x,rp,body)) paramdecls in
              let projtyp =
                it_mkProd_or_LetIn (mkProd (x,rp,ccl)) paramdecls in
	      let kn =
	        try
		  let cie = {
		    const_entry_body = proj;
                    const_entry_type = Some projtyp;
                    const_entry_opaque = false;
		    const_entry_boxed = Flags.boxed_definitions() } in
		  let k = (DefinitionEntry cie,IsDefinition kind) in
		  let kn = declare_internal_constant fid k in
		  Flags.if_verbose message (string_of_id fid ^" is defined");
		  kn
                with Type_errors.TypeError (ctx,te) ->
                  raise (NotDefinable (BadTypedProj (fid,ctx,te))) in
	      let refi = ConstRef kn in
	      let constr_fi = mkConst kn in
	      Impargs.maybe_declare_manual_implicits false refi impls;
	      if coe then begin
	        let cl = Class.class_of_global (IndRef indsp) in
	        Class.try_add_new_coercion_with_source refi Global cl
	      end;
	      let proj_args = (*Rel 1 refers to "x"*) paramargs@[mkRel 1] in
	      let constr_fip = applist (constr_fi,proj_args) in
	      (Some kn::sp_projs, Projection constr_fip::subst)
            with NotDefinable why ->
	      warning_or_error coe indsp why;
	      (None::sp_projs,NoProjection fi::subst) in
      (nfi-1,(fi, optci=None)::kinds,sp_projs,subst))
      (List.length fields,[],[],[]) coers (List.rev fields) (List.rev fieldimpls)
  in (kinds,sp_projs)

let structure_signature ctx =
  let rec deps_to_evar evm l =
    match l with [] -> Evd.empty
      | [(_,_,typ)] -> Evd.add evm (Evarutil.new_untyped_evar())
	  (Evd.make_evar Environ.empty_named_context_val typ)
      | (_,_,typ)::tl ->
	  let ev = Evarutil.new_untyped_evar() in
	  let evm = Evd.add evm ev (Evd.make_evar Environ.empty_named_context_val typ) in
	  let new_tl = Util.list_map_i
	    (fun pos (n,c,t) -> n,c,
	       Termops.replace_term (mkRel pos) (mkEvar(ev,[||])) t) 1 tl in
	  deps_to_evar evm new_tl in
  deps_to_evar Evd.empty (List.rev ctx)

open Typeclasses

let declare_structure finite infer id idbuild paramimpls params arity fieldimpls fields
    ?(kind=StructureComponent) ?name is_coe coers sign =
  let nparams = List.length params and nfields = List.length fields in
  let args = extended_rel_list nfields params in
  let ind = applist (mkRel (1+nparams+nfields), args) in
  let type_constructor = it_mkProd_or_LetIn ind fields in
  let mie_ind =
    { mind_entry_typename = id;
      mind_entry_arity = arity;
      mind_entry_consnames = [idbuild];
      mind_entry_lc = [type_constructor] }
  in
  (* spiwack: raises an error if the structure is supposed to be non-recursive,
        but isn't *)
  (* there is probably a way to push this to "declare_mutual" *)
  begin match  finite with
  | BiFinite ->
      if dependent (mkRel (nparams+1)) (it_mkProd_or_LetIn mkProp fields) then
	error "Records declared with the keyword Record or Structure cannot be recursive. Maybe you meant to define an Inductive or CoInductive record."
  | _ -> ()
  end;
  let mie =
    { mind_entry_params = List.map degenerate_decl params;
      mind_entry_record = true;
      mind_entry_finite = recursivity_flag_of_kind finite;
      mind_entry_inds = [mie_ind] } in
  let kn = Command.declare_mutual_inductive_with_eliminations KernelVerbose mie [(paramimpls,[])] in
  let rsp = (kn,0) in (* This is ind path of idstruc *)
  let cstr = (rsp,1) in
  let kinds,sp_projs = declare_projections rsp ~kind ?name coers fieldimpls fields in
  let build = ConstructRef cstr in
  if is_coe then Class.try_add_new_coercion build Global;
  Recordops.declare_structure(rsp,cstr,List.rev kinds,List.rev sp_projs);
  if infer then
    Evd.fold (fun ev evi () -> Recordops.declare_method (ConstructRef cstr) ev sign) sign ();
  rsp

let implicits_of_context ctx =
  list_map_i (fun i name ->
    let explname =
      match name with
      | Name n -> Some n
      | Anonymous -> None
    in ExplByPos (i, explname), (true, true, true))
    1 (List.rev (Anonymous :: (List.map pi1 ctx)))

let qualid_of_con c = 
  Qualid (dummy_loc, shortest_qualid_of_global Idset.empty (ConstRef c))

let declare_instance_cst glob con =
  let instance = Typeops.type_of_constant (Global.env ()) con in
  let _, r = decompose_prod_assum instance in
    match class_of_constr r with
      | Some tc -> add_instance (new_instance tc None glob (ConstRef con))
      | None -> errorlabstrm "" (Pp.strbrk "Constant does not build instances of a declared type class.")

let declare_class finite def infer id idbuild paramimpls params arity fieldimpls fields
    ?(kind=StructureComponent) ?name is_coe coers sign =
  let fieldimpls =
    (* Make the class and all params implicits in the projections *)
    let ctx_impls = implicits_of_context params in
    let len = succ (List.length params) in
      List.map (fun x -> ctx_impls @ Impargs.lift_implicits len x) fieldimpls
  in
  let impl, projs =
    match fields with
    | [(Name proj_name, _, field)] when def ->
	let class_body = it_mkLambda_or_LetIn field params in
	let class_type = Option.map (fun ar -> it_mkProd_or_LetIn ar params) arity in
	let class_entry =
	  { const_entry_body = class_body;
	    const_entry_type = class_type;
	    const_entry_opaque = false;
	    const_entry_boxed = false }
	in
	let cst = Declare.declare_constant (snd id)
	  (DefinitionEntry class_entry, IsDefinition Definition)
	in
	let inst_type = appvectc (mkConst cst) (rel_vect 0 (List.length params)) in
	let proj_type = it_mkProd_or_LetIn (mkProd(Name (snd id), inst_type, lift 1 field)) params in
	let proj_body = it_mkLambda_or_LetIn (mkLambda (Name (snd id), inst_type, mkRel 1)) params in
	let proj_entry =
	  { const_entry_body = proj_body;
	    const_entry_type = Some proj_type;
	    const_entry_opaque = false;
	    const_entry_boxed = false }
	in
	let proj_cst = Declare.declare_constant proj_name
	  (DefinitionEntry proj_entry, IsDefinition Definition)
	in
	let cref = ConstRef cst in
	Impargs.declare_manual_implicits false cref paramimpls;
	Impargs.declare_manual_implicits false (ConstRef proj_cst) (List.hd fieldimpls);
	Classes.set_typeclass_transparency (EvalConstRef cst) false;
	if infer then Evd.fold (fun ev evi _ -> Recordops.declare_method (ConstRef cst) ev sign) sign ();
	cref, [proj_name, Some proj_cst]
    | _ ->
	let idarg = Namegen.next_ident_away (snd id) (ids_of_context (Global.env())) in
	let ind = declare_structure BiFinite infer (snd id) idbuild paramimpls
	  params (Option.cata (fun x -> x) (new_Type ()) arity) fieldimpls fields
	  ~kind:Method ~name:idarg false (List.map (fun _ -> false) fields) sign
	in
	  IndRef ind, (List.map2 (fun (id, _, _) y -> (Nameops.out_name id, y))
			     (List.rev fields) (Recordops.lookup_projections ind))
  in
  let ctx_context =
    List.map (fun (na, b, t) ->
      match Typeclasses.class_of_constr t with
      | Some cl -> Some (cl.cl_impl, true) (*List.exists (fun (_, n) -> n = na) supnames)*)
      | None -> None)
      params, params
  in
  let k =
    { cl_impl = impl;
      cl_context = ctx_context;
      cl_props = fields;
      cl_projs = projs }
  in
    List.iter2 (fun p sub ->
      if sub then match snd p with Some p -> declare_instance_cst true p | None -> ())
      k.cl_projs coers;
  add_class k; impl

let interp_and_check_sort sort =
  Option.map (fun sort ->
    let env = Global.env() and sigma = Evd.empty in
    let s = interp_constr sigma env sort in
    if isSort (Reductionops.whd_betadeltaiota env sigma s) then s
    else user_err_loc (constr_loc sort,"", str"Sort expected.")) sort

open Vernacexpr
open Autoinstance

(* [fs] corresponds to fields and [ps] to parameters; [coers] is a boolean
   list telling if the corresponding fields must me declared as coercion *)
let definition_structure (kind,finite,infer,(is_coe,(loc,idstruc)),ps,cfs,idbuild,s) =
  let cfs,notations = List.split cfs in
  let coers,fs = List.split cfs in
  let extract_name acc = function
      Vernacexpr.AssumExpr((_,Name id),_) -> id::acc
    | Vernacexpr.DefExpr ((_,Name id),_,_) -> id::acc
    | _ -> acc in
  let allnames =  idstruc::(List.fold_left extract_name [] fs) in
  if not (list_distinct allnames) then error "Two objects have the same name";
  (* Now, younger decl in params and fields is on top *)
  let sc = interp_and_check_sort s in
  let implpars, params, implfs, fields =
    States.with_state_protection (fun () ->
      typecheck_params_and_fields idstruc sc ps notations fs) () in
  let sign = structure_signature (fields@params) in
    match kind with
    | Class def ->
	let gr = declare_class finite def infer (loc,idstruc) idbuild
	  implpars params sc implfs fields is_coe coers sign in
	if infer then search_record declare_class_instance gr sign;
	gr
    | _ ->
	let arity = Option.default (new_Type ()) sc in
	let implfs = List.map
	  (fun impls -> implpars @ Impargs.lift_implicits (succ (List.length params)) impls) implfs in
	let ind = declare_structure finite infer idstruc idbuild implpars params arity implfs fields is_coe coers sign in
	if infer then search_record declare_record_instance (ConstructRef (ind,1)) sign;
	IndRef ind
