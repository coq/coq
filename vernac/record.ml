(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Globnames
open Nameops
open Term
open Vars
open Environ
open Declarations
open Entries
open Declare
open Constrintern
open Decl_kinds
open Type_errors
open Constrexpr
open Constrexpr_ops
open Goptions
open Sigma.Notations
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration

(********** definition d'un record (structure) **************)

(** Flag governing use of primitive projections. Disabled by default. *)
let primitive_flag = ref false
let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "use of primitive projections";
      optkey   = ["Primitive";"Projections"];
      optread  = (fun () -> !primitive_flag) ;
      optwrite = (fun b -> primitive_flag := b) }

let typeclasses_strict = ref false
let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "strict typeclass resolution";
      optkey   = ["Typeclasses";"Strict";"Resolution"];
      optread  = (fun () -> !typeclasses_strict);
      optwrite = (fun b -> typeclasses_strict := b); }

let typeclasses_unique = ref false
let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "unique typeclass instances";
      optkey   = ["Typeclasses";"Unique";"Instances"];
      optread  = (fun () -> !typeclasses_unique);
      optwrite = (fun b -> typeclasses_unique := b); }

let interp_fields_evars env evars impls_env nots l =
  List.fold_left2
    (fun (env, uimpls, params, impls) no ((loc, i), b, t) ->
      let t', impl = interp_type_evars_impls env evars ~impls t in
      let b' = Option.map (fun x -> EConstr.Unsafe.to_constr (fst (interp_casted_constr_evars_impls env evars ~impls x t'))) b in
      let t' = EConstr.Unsafe.to_constr t' in
      let impls =
	match i with
	| Anonymous -> impls
	| Name id -> Id.Map.add id (compute_internalization_data env Constrintern.Method t' impl) impls
      in
      let d = match b' with
	      | None -> LocalAssum (i,t')
	      | Some b' -> LocalDef (i,b',t')
      in
      List.iter (Metasyntax.set_notation_for_interpretation impls) no;
      (push_rel d env, impl :: uimpls, d::params, impls))
    (env, [], [], impls_env) nots l

let compute_constructor_level evars env l =
  List.fold_right (fun d (env, univ) ->
    let univ = 
      if is_local_assum d then
	let s = Retyping.get_sort_of env evars (EConstr.of_constr (RelDecl.get_type d)) in
	  Univ.sup (univ_of_sort s) univ 
      else univ
    in (push_rel d env, univ)) 
    l (env, Univ.type0m_univ)

let binder_of_decl = function
  | Vernacexpr.AssumExpr(n,t) -> (n,None,t)
  | Vernacexpr.DefExpr(n,c,t) -> (n,Some c, match t with Some c -> c
                                                       | None   -> CAst.make ?loc:(fst n) @@ CHole (None, Misctypes.IntroAnonymous, None))

let binders_of_decls = List.map binder_of_decl

let typecheck_params_and_fields def id pl t ps nots fs =
  let env0 = Global.env () in
  let ctx = Evd.make_evar_universe_context env0 pl in
  let evars = ref (Evd.from_ctx ctx) in
  let _ = 
    let error bk (loc, name) = 
      match bk, name with
      | Default _, Anonymous ->
        user_err ?loc ~hdr:"record" (str "Record parameters must be named")
      | _ -> ()
    in
      List.iter 
	(function CLocalDef (b, _, _) -> error default_binder_kind b
	   | CLocalAssum (ls, bk, ce) -> List.iter (error bk) ls
           | CLocalPattern (loc,(_,_)) ->
              Loc.raise ?loc (Stream.Error "pattern with quote not allowed in record parameters.")) ps
  in 
  let impls_env, ((env1,newps), imps) = interp_context_evars env0 evars ps in
  let newps = List.map (fun d -> Termops.map_rel_decl EConstr.Unsafe.to_constr d) newps in
  let t', template = match t with 
    | Some t -> 
       let env = push_rel_context newps env0 in
       let poly =
         match t with
         | { CAst.v = CSort (Misctypes.GType []) } -> true | _ -> false in
       let s = interp_type_evars env evars ~impls:empty_internalization_env t in
       let sred = Reductionops.whd_all env !evars s in
       let s = EConstr.Unsafe.to_constr s in
       let sred = EConstr.Unsafe.to_constr sred in
	 (match kind_of_term sred with
	 | Sort s' -> 
	    (if poly then
               match Evd.is_sort_variable !evars s' with
	       | Some l -> evars := Evd.make_flexible_variable !evars true l; 
	                  sred, true
	       | None -> s, false
             else s, false)
	 | _ -> user_err ?loc:(constr_loc t) (str"Sort expected."))
    | None -> 
      let uvarkind = Evd.univ_flexible_alg in
	mkSort (Evarutil.evd_comb0 (Evd.new_sort_variable uvarkind) evars), true
  in
  let fullarity = it_mkProd_or_LetIn t' newps in
  let env_ar = push_rel_context newps (push_rel (LocalAssum (Name id,fullarity)) env0) in
  let env2,impls,newfs,data =
    interp_fields_evars env_ar evars impls_env nots (binders_of_decls fs)
  in
  let sigma = 
    Pretyping.solve_remaining_evars Pretyping.all_and_fail_flags env_ar !evars Evd.empty in
  let evars, nf = Evarutil.nf_evars_and_universes sigma in
  let arity = nf t' in
  let arity, evars = 
    let _, univ = compute_constructor_level evars env_ar newfs in
    let ctx, aritysort = Reduction.dest_arity env0 arity in
      assert(List.is_empty ctx); (* Ensured by above analysis *)
      if not def && (Sorts.is_prop aritysort || 
	(Sorts.is_set aritysort && is_impredicative_set env0)) then
	arity, evars
      else
	let evars = Evd.set_leq_sort env_ar evars (Type univ) aritysort in
	if Univ.is_small_univ univ &&
	   Option.cata (Evd.is_flexible_level evars) false (Evd.is_sort_variable evars aritysort) then
	   (* We can assume that the level in aritysort is not constrained
	       and clear it, if it is flexible *)
	  mkArity (ctx, Sorts.sort_of_univ univ),
	  Evd.set_eq_sort env_ar evars (Prop Pos) aritysort
	else arity, evars
  in
  let evars, nf = Evarutil.nf_evars_and_universes evars in
  let newps = Context.Rel.map nf newps in
  let newfs = Context.Rel.map nf newfs in
  let ce t = Pretyping.check_evars env0 Evd.empty evars (EConstr.of_constr t) in
    List.iter (iter_constr ce) (List.rev newps);
    List.iter (iter_constr ce) (List.rev newfs);
    Evd.universe_context ?names:pl evars, nf arity, template, imps, newps, impls, newfs

let degenerate_decl decl =
  let id = match RelDecl.get_name decl with
    | Name id -> id
    | Anonymous -> anomaly (Pp.str "Unnamed record variable") in
  match decl with
    | LocalAssum (_,t) -> (id, LocalAssumEntry t)
    | LocalDef (_,b,_) -> (id, LocalDefEntry b)

type record_error =
  | MissingProj of Id.t * Id.t list
  | BadTypedProj of Id.t * env * Type_errors.type_error

let warn_cannot_define_projection =
  CWarnings.create ~name:"cannot-define-projection" ~category:"records"
         (fun msg -> hov 0 msg)

(* If a projection is not definable, we throw an error if the user
asked it to be a coercion. Otherwise, we just print an info
message. The user might still want to name the field of the record. *)
let warning_or_error coe indsp err =
  let st = match err with
    | MissingProj (fi,projs) ->
	let s,have = if List.length projs > 1 then "s","were" else "","was" in
        (pr_id fi ++
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
  if coe then user_err ~hdr:"structure" st;
  warn_cannot_define_projection (hov 0 st)

type field_status =
  | NoProjection of Name.t
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
	    | NoProjection Anonymous ->
                user_err  (str "Field " ++ pr_id fid ++
                  str " depends on the " ++ pr_nth (k-depth-1) ++ str
                  " field which has no name.")
        else
	  mkRel (k-lv)
    | _ -> map_constr_with_binders succ substrec depth c
  in
  let c' = lift 1 c in (* to get [c] defined in ctxt [[params;fields;x:ind]] *)
  let c'' = substrec 0 c' in
  if not (List.is_empty !bad_projs) then
    raise (NotDefinable (MissingProj (fid,List.rev !bad_projs)));
  c''

let instantiate_possibly_recursive_type indu paramdecls fields =
  let subst = List.map_i (fun i _ -> mkRel i) 1 paramdecls in
  Termops.substl_rel_context (subst@[mkIndU indu]) fields

let warn_non_primitive_record =
  CWarnings.create ~name:"non-primitive-record" ~category:"record"
         (fun (env,indsp) ->
          (hov 0 (str "The record " ++ Printer.pr_inductive env indsp ++ 
                    strbrk" could not be defined as a primitive record")))

(* We build projections *)
let declare_projections indsp ?(kind=StructureComponent) binder_name coers fieldimpls fields =
  let env = Global.env() in
  let (mib,mip) = Global.lookup_inductive indsp in
  let u = Declareops.inductive_instance mib in
  let paramdecls = Inductive.inductive_paramdecls (mib, u) in
  let poly = mib.mind_polymorphic in
  let ctx = Univ.instantiate_univ_context mib.mind_universes in
  let indu = indsp, u in
  let r = mkIndU (indsp,u) in
  let rp = applist (r, Context.Rel.to_extended_list mkRel 0 paramdecls) in
  let paramargs = Context.Rel.to_extended_list mkRel 1 paramdecls in (*def in [[params;x:rp]]*)
  let x = Name binder_name in
  let fields = instantiate_possibly_recursive_type indu paramdecls fields in
  let lifted_fields = Termops.lift_rel_context 1 fields in
  let primitive = 
    if !primitive_flag then 
      let is_primitive = 
	match mib.mind_record with
	| Some (Some _) -> true
	| Some None | None -> false
      in
	if not is_primitive then 
	  warn_non_primitive_record (env,indsp);
	is_primitive
    else false
  in
  let (_,_,kinds,sp_projs,_) =
    List.fold_left3
      (fun (nfi,i,kinds,sp_projs,subst) coe decl impls ->
        let fi = RelDecl.get_name decl in
        let ti = RelDecl.get_type decl in
	let (sp_projs,i,subst) =
	  match fi with
	  | Anonymous ->
	      (None::sp_projs,i,NoProjection fi::subst)
	  | Name fid -> try
	    let kn, term = 
	      if is_local_assum decl && primitive then
		(** Already defined in the kernel silently *)
		let kn = destConstRef (Nametab.locate (Libnames.qualid_of_ident fid)) in
		  Declare.definition_message fid;
		  kn, mkProj (Projection.make kn false,mkRel 1)
	      else
		let ccl = subst_projection fid subst ti in
		let body = match decl with
		  | LocalDef (_,ci,_) -> subst_projection fid subst ci
		  | LocalAssum _ ->
	            (* [ccl] is defined in context [params;x:rp] *)
		    (* [ccl'] is defined in context [params;x:rp;x:rp] *)
		    let ccl' = liftn 1 2 ccl in
		    let p = mkLambda (x, lift 1 rp, ccl') in
		    let branch = it_mkLambda_or_LetIn (mkRel nfi) lifted_fields in
		    let ci = Inductiveops.make_case_info env indsp LetStyle in
		      mkCase (ci, p, mkRel 1, [|branch|]) 
		in
		let proj =
	          it_mkLambda_or_LetIn (mkLambda (x,rp,body)) paramdecls in
		let projtyp =
                  it_mkProd_or_LetIn (mkProd (x,rp,ccl)) paramdecls in
	        try
		  let entry = {
		    const_entry_body =
		      Future.from_val (Safe_typing.mk_pure_proof proj);
		    const_entry_secctx = None;
		    const_entry_type = Some projtyp;
		    const_entry_polymorphic = poly;
		    const_entry_universes =
		      if poly then ctx else Univ.UContext.empty;
		    const_entry_opaque = false;
		    const_entry_inline_code = false;
		    const_entry_feedback = None } in
		  let k = (DefinitionEntry entry,IsDefinition kind) in
		  let kn = declare_constant ~internal:InternalTacticRequest fid k in
		  let constr_fip =
		    let proj_args = (*Rel 1 refers to "x"*) paramargs@[mkRel 1] in
		      applist (mkConstU (kn,u),proj_args) 
		  in
		    Declare.definition_message fid;
		    kn, constr_fip
                with Type_errors.TypeError (ctx,te) ->
                  raise (NotDefinable (BadTypedProj (fid,ctx,te))) 
	    in
	    let refi = ConstRef kn in
	    Impargs.maybe_declare_manual_implicits false refi impls;
	    if coe then begin
	      let cl = Class.class_of_global (IndRef indsp) in
	        Class.try_add_new_coercion_with_source refi ~local:false poly ~source:cl
	    end;
	    let i = if is_local_assum decl then i+1 else i in
	      (Some kn::sp_projs, i, Projection term::subst)
            with NotDefinable why ->
	      warning_or_error coe indsp why;
	      (None::sp_projs,i,NoProjection fi::subst) in
      (nfi-1,i,(fi, is_local_assum decl)::kinds,sp_projs,subst))
      (List.length fields,0,[],[],[]) coers (List.rev fields) (List.rev fieldimpls)
  in (kinds,sp_projs)

let structure_signature ctx =
  let rec deps_to_evar evm l =
    match l with [] -> Evd.empty
      | [decl] ->
        let env = Environ.empty_named_context_val in
        let evm = Sigma.Unsafe.of_evar_map evm in
        let Sigma (_, evm, _) = Evarutil.new_pure_evar env evm (EConstr.of_constr (RelDecl.get_type decl)) in
        let evm = Sigma.to_evar_map evm in
        evm
      | decl::tl ->
          let env = Environ.empty_named_context_val in
          let evm = Sigma.Unsafe.of_evar_map evm in
          let Sigma (ev, evm, _) = Evarutil.new_pure_evar env evm (EConstr.of_constr (RelDecl.get_type decl)) in
          let evm = Sigma.to_evar_map evm in
	  let new_tl = Util.List.map_i
	    (fun pos decl ->
	       RelDecl.map_type (fun t -> EConstr.Unsafe.to_constr (Termops.replace_term evm (EConstr.mkRel pos) (EConstr.mkEvar(ev,[||])) (EConstr.of_constr t))) decl) 1 tl in
	  deps_to_evar evm new_tl in
  deps_to_evar Evd.empty (List.rev ctx)

open Typeclasses

let declare_structure finite poly ctx id idbuild paramimpls params arity template 
    fieldimpls fields ?(kind=StructureComponent) ?name is_coe coers sign =
  let nparams = List.length params and nfields = List.length fields in
  let args = Context.Rel.to_extended_list mkRel nfields params in
  let ind = applist (mkRel (1+nparams+nfields), args) in
  let type_constructor = it_mkProd_or_LetIn ind fields in
  let binder_name = 
    match name with
    | None -> Id.of_string (Unicode.lowercase_first_char (Id.to_string id)) 
    | Some n -> n
  in
  let mie_ind =
    { mind_entry_typename = id;
      mind_entry_arity = arity;
      mind_entry_template = not poly && template;
      mind_entry_consnames = [idbuild];
      mind_entry_lc = [type_constructor] }
  in
  let mie =
    { mind_entry_params = List.map degenerate_decl params;
      mind_entry_record = Some (if !primitive_flag then Some binder_name else None);
      mind_entry_finite = finite;
      mind_entry_inds = [mie_ind];
      mind_entry_polymorphic = poly;
      mind_entry_private = None;
      mind_entry_universes = ctx;
    }
  in
  let kn = Command.declare_mutual_inductive_with_eliminations mie [] [(paramimpls,[])] in
  let rsp = (kn,0) in (* This is ind path of idstruc *)
  let cstr = (rsp,1) in
  let kinds,sp_projs = declare_projections rsp ~kind binder_name coers fieldimpls fields in
  let build = ConstructRef cstr in
  let () = if is_coe then Class.try_add_new_coercion build ~local:false poly in
  Recordops.declare_structure(rsp,cstr,List.rev kinds,List.rev sp_projs);
  rsp

let implicits_of_context ctx =
  List.map_i (fun i name ->
    let explname =
      match name with
      | Name n -> Some n
      | Anonymous -> None
    in ExplByPos (i, explname), (true, true, true))
    1 (List.rev (Anonymous :: (List.map RelDecl.get_name ctx)))

let declare_class finite def poly ctx id idbuild paramimpls params arity 
    template fieldimpls fields ?(kind=StructureComponent) is_coe coers priorities sign =
  let fieldimpls =
    (* Make the class implicit in the projections, and the params if applicable. *)
    let len = List.length params in
    let impls = implicits_of_context params in
      List.map (fun x -> impls @ Impargs.lift_implicits (succ len) x) fieldimpls
  in
  let binder_name = Namegen.next_ident_away (snd id) (Termops.ids_of_context (Global.env())) in
  let impl, projs =
    match fields with
    | [LocalAssum (Name proj_name, field) | LocalDef (Name proj_name, _, field)] when def ->
      let class_body = it_mkLambda_or_LetIn field params in
      let class_type = it_mkProd_or_LetIn arity params in
      let class_entry = 
	Declare.definition_entry ~types:class_type ~poly ~univs:ctx class_body in
      let cst = Declare.declare_constant (snd id)
	(DefinitionEntry class_entry, IsDefinition Definition)
      in
      let cstu = (cst, if poly then Univ.UContext.instance ctx else Univ.Instance.empty) in
      let inst_type = appvectc (mkConstU cstu)
			       (Termops.rel_vect 0 (List.length params)) in
      let proj_type =
	it_mkProd_or_LetIn (mkProd(Name binder_name, inst_type, lift 1 field)) params in
      let proj_body =
	it_mkLambda_or_LetIn (mkLambda (Name binder_name, inst_type, mkRel 1)) params in
      let proj_entry =
	Declare.definition_entry ~types:proj_type ~poly
	    ~univs:(if poly then ctx else Univ.UContext.empty) proj_body
      in
      let proj_cst = Declare.declare_constant proj_name
        (DefinitionEntry proj_entry, IsDefinition Definition)
      in
      let cref = ConstRef cst in
      Impargs.declare_manual_implicits false cref [paramimpls];
      Impargs.declare_manual_implicits false (ConstRef proj_cst) [List.hd fieldimpls];
      Classes.set_typeclass_transparency (EvalConstRef cst) false false;
      let sub = match List.hd coers with
	| Some b -> Some ((if b then Backward else Forward), List.hd priorities) 
	| None -> None 
      in
      cref, [Name proj_name, sub, Some proj_cst]
    | _ ->
       let ind = declare_structure BiFinite poly ctx (snd id) idbuild paramimpls
	  params arity template fieldimpls fields
	  ~kind:Method ~name:binder_name false (List.map (fun _ -> false) fields) sign
       in
       let coers = List.map2 (fun coe pri -> 
			      Option.map (fun b -> 
			      if b then Backward, pri else Forward, pri) coe)
	  coers priorities
       in
       let l = List.map3 (fun decl b y -> RelDecl.get_name decl, b, y)
         (List.rev fields) coers (Recordops.lookup_projections ind)
       in IndRef ind, l
  in
  let ctx_context =
    List.map (fun decl ->
      match Typeclasses.class_of_constr Evd.empty (EConstr.of_constr (RelDecl.get_type decl)) with
      | Some (_, ((cl,_), _)) -> Some (cl.cl_impl, true)
      | None -> None)
      params, params
  in
  let k =
    { cl_impl = impl;
      cl_strict = !typeclasses_strict;
      cl_unique = !typeclasses_unique;
      cl_context = ctx_context;
      cl_props = fields;
      cl_projs = projs }
  in
    add_class k; impl


let add_constant_class cst =
  let ty = Universes.unsafe_type_of_global (ConstRef cst) in
  let ctx, arity = decompose_prod_assum ty in
  let tc = 
    { cl_impl = ConstRef cst;
      cl_context = (List.map (const None) ctx, ctx);
      cl_props = [LocalAssum (Anonymous, arity)];
      cl_projs = [];
      cl_strict = !typeclasses_strict;
      cl_unique = !typeclasses_unique
    }
  in add_class tc;
    set_typeclass_transparency (EvalConstRef cst) false false
      
let add_inductive_class ind =
  let mind, oneind = Global.lookup_inductive ind in
  let k =
    let ctx = oneind.mind_arity_ctxt in
    let inst = Univ.UContext.instance mind.mind_universes in
    let ty = Inductive.type_of_inductive
      (push_rel_context ctx (Global.env ()))
      ((mind,oneind),inst)
    in
      { cl_impl = IndRef ind;
	cl_context = List.map (const None) ctx, ctx;
	cl_props = [LocalAssum (Anonymous, ty)];
	cl_projs = [];
	cl_strict = !typeclasses_strict;
	cl_unique = !typeclasses_unique }
  in add_class k

let declare_existing_class g =
  match g with
  | ConstRef x -> add_constant_class x
  | IndRef x -> add_inductive_class x
  | _ -> user_err ~hdr:"declare_existing_class"
		      (Pp.str"Unsupported class type, only constants and inductives are allowed")

open Vernacexpr

(* [fs] corresponds to fields and [ps] to parameters; [coers] is a
   list telling if the corresponding fields must me declared as coercions 
   or subinstances. *)
let definition_structure (kind,poly,finite,(is_coe,((loc,idstruc),pl)),ps,cfs,idbuild,s) =
  let cfs,notations = List.split cfs in
  let cfs,priorities = List.split cfs in
  let coers,fs = List.split cfs in
  let extract_name acc = function
      Vernacexpr.AssumExpr((_,Name id),_) -> id::acc
    | Vernacexpr.DefExpr ((_,Name id),_,_) -> id::acc
    | _ -> acc in
  let allnames =  idstruc::(List.fold_left extract_name [] fs) in
  let () = match List.duplicates Id.equal allnames with
  | [] -> ()
  | id :: _ -> user_err (str "Two objects have the same name" ++ spc () ++ quote (Id.print id))
  in
  let isnot_class = match kind with Class false -> false | _ -> true in
  if isnot_class && List.exists (fun opt -> not (Option.is_empty opt)) priorities then
    error "Priorities only allowed for type class substructures";
  (* Now, younger decl in params and fields is on top *)
  let (pl, ctx), arity, template, implpars, params, implfs, fields =
    States.with_state_protection (fun () ->
      typecheck_params_and_fields (kind = Class true) idstruc pl s ps notations fs) () in
  let sign = structure_signature (fields@params) in
  let gr = match kind with
  | Class def ->
     let priorities = List.map (fun id -> {hint_priority = id; hint_pattern = None}) priorities in
     let gr = declare_class finite def poly ctx (loc,idstruc) idbuild
	  implpars params arity template implfs fields is_coe coers priorities sign in
	gr
    | _ ->
	let implfs = List.map
	  (fun impls -> implpars @ Impargs.lift_implicits
	    (succ (List.length params)) impls) implfs in
	let ind = declare_structure finite poly ctx idstruc
	  idbuild implpars params arity template implfs 
	  fields is_coe (List.map (fun coe -> not (Option.is_empty coe)) coers) sign in
	IndRef ind
  in
  Universes.register_universe_binders gr pl;
  gr
