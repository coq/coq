(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Term
open Sorts
open Util
open Names
open Globnames
open Nameops
open Constr
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
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration

(********** definition d'un record (structure) **************)

(** Flag governing use of primitive projections. Disabled by default. *)
let primitive_flag = ref false
let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "use of primitive projections";
      optkey   = ["Primitive";"Projections"];
      optread  = (fun () -> !primitive_flag) ;
      optwrite = (fun b -> primitive_flag := b) }

let typeclasses_strict = ref false
let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "strict typeclass resolution";
      optkey   = ["Typeclasses";"Strict";"Resolution"];
      optread  = (fun () -> !typeclasses_strict);
      optwrite = (fun b -> typeclasses_strict := b); }

let typeclasses_unique = ref false
let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "unique typeclass instances";
      optkey   = ["Typeclasses";"Unique";"Instances"];
      optread  = (fun () -> !typeclasses_unique);
      optwrite = (fun b -> typeclasses_unique := b); }

let interp_fields_evars env sigma impls_env nots l =
  List.fold_left2
    (fun (env, sigma, uimpls, params, impls) no ({CAst.loc;v=i}, b, t) ->
      let sigma, (t', impl) = interp_type_evars_impls env sigma ~impls t in
      let sigma, b' =
        Option.cata (fun x -> on_snd (fun x -> Some (fst x)) @@
                      interp_casted_constr_evars_impls env sigma ~impls x t') (sigma,None) b in
      let impls =
	match i with
	| Anonymous -> impls
        | Name id -> Id.Map.add id (compute_internalization_data env sigma Constrintern.Method t' impl) impls
      in
      let d = match b' with
	      | None -> LocalAssum (i,t')
	      | Some b' -> LocalDef (i,b',t')
      in
      List.iter (Metasyntax.set_notation_for_interpretation env impls) no;
      (EConstr.push_rel d env, sigma, impl :: uimpls, d::params, impls))
    (env, sigma, [], [], impls_env) nots l

let compute_constructor_level evars env l =
  List.fold_right (fun d (env, univ) ->
    let univ = 
      if is_local_assum d then
	let s = Retyping.get_sort_of env evars (RelDecl.get_type d) in
	  Univ.sup (univ_of_sort s) univ 
      else univ
    in (EConstr.push_rel d env, univ))
    l (env, Univ.type0m_univ)

let binder_of_decl = function
  | Vernacexpr.AssumExpr(n,t) -> (n,None,t)
  | Vernacexpr.DefExpr(n,c,t) ->
    (n,Some c, match t with Some c -> c
                          | None   -> CAst.make ?loc:n.CAst.loc @@ CHole (None, Misctypes.IntroAnonymous, None))

let binders_of_decls = List.map binder_of_decl

let typecheck_params_and_fields finite def id poly pl t ps nots fs =
  let env0 = Global.env () in
  let sigma, decl = Univdecls.interp_univ_decl_opt env0 pl in
  let _ =
    let error bk {CAst.loc; v=name} =
      match bk, name with
      | Default _, Anonymous ->
        user_err ?loc ~hdr:"record" (str "Record parameters must be named")
      | _ -> ()
    in
      List.iter 
	(function CLocalDef (b, _, _) -> error default_binder_kind b
	   | CLocalAssum (ls, bk, ce) -> List.iter (error bk) ls
           | CLocalPattern {CAst.loc} ->
              Loc.raise ?loc (Stream.Error "pattern with quote not allowed in record parameters.")) ps
  in 
  let sigma, (impls_env, ((env1,newps), imps)) = interp_context_evars env0 sigma ps in
  let sigma, typ, sort, template = match t with
    | Some t -> 
       let env = EConstr.push_rel_context newps env0 in
       let poly =
         match t with
         | { CAst.v = CSort (Misctypes.GType []) } -> true | _ -> false in
       let sigma, s = interp_type_evars env sigma ~impls:empty_internalization_env t in
       let sred = Reductionops.whd_allnolet env sigma s in
         (match EConstr.kind sigma sred with
	 | Sort s' ->
            let s' = EConstr.ESorts.kind sigma s' in
	    (if poly then
               match Evd.is_sort_variable sigma s' with
               | Some l ->
                 let sigma = Evd.make_flexible_variable sigma ~algebraic:true l in
                 sigma, s, s', true
               | None ->
                 sigma, s, s', false
             else sigma, s, s', false)
	 | _ -> user_err ?loc:(constr_loc t) (str"Sort expected."))
    | None -> 
      let uvarkind = Evd.univ_flexible_alg in
      let sigma, s = Evd.new_sort_variable uvarkind sigma in
      sigma, EConstr.mkSort s, s, true
  in
  let arity = EConstr.it_mkProd_or_LetIn typ newps in
  let env_ar = EConstr.push_rel_context newps (EConstr.push_rel (LocalAssum (Name id,arity)) env0) in
  let assums = List.filter is_local_assum newps in
  let params = List.map (RelDecl.get_name %> Name.get_id) assums in
  let ty = Inductive (params,(finite != Declarations.BiFinite)) in
  let impls_env = compute_internalization_env env0 sigma ~impls:impls_env ty [id] [arity] [imps] in
  let env2,sigma,impls,newfs,data =
    interp_fields_evars env_ar sigma impls_env nots (binders_of_decls fs)
  in
  let sigma =
    Pretyping.solve_remaining_evars Pretyping.all_and_fail_flags env_ar sigma Evd.empty in
  let sigma, typ =
    let _, univ = compute_constructor_level sigma env_ar newfs in
      if not def && (Sorts.is_prop sort ||
	(Sorts.is_set sort && is_impredicative_set env0)) then
        sigma, typ
      else
        let sigma = Evd.set_leq_sort env_ar sigma (Type univ) sort in
	if Univ.is_small_univ univ &&
           Option.cata (Evd.is_flexible_level sigma) false (Evd.is_sort_variable sigma sort) then
	   (* We can assume that the level in aritysort is not constrained
	       and clear it, if it is flexible *)
          Evd.set_eq_sort env_ar sigma (Prop Pos) sort,
          EConstr.mkSort (Sorts.sort_of_univ univ)
        else sigma, typ
  in
  let sigma, _ = Evarutil.nf_evars_and_universes sigma in
  let newfs = List.map (EConstr.to_rel_decl sigma) newfs in
  let newps = List.map (EConstr.to_rel_decl sigma) newps in
  let typ = EConstr.to_constr sigma typ in
  let ce t = Pretyping.check_evars env0 Evd.empty sigma (EConstr.of_constr t) in
  let univs = Evd.check_univ_decl ~poly sigma decl in
  let ubinders = Evd.universe_binders sigma in
    List.iter (iter_constr ce) (List.rev newps);
    List.iter (iter_constr ce) (List.rev newfs);
    ubinders, univs, typ, template, imps, newps, impls, newfs

let degenerate_decl decl =
  let id = match RelDecl.get_name decl with
    | Name id -> id
    | Anonymous -> anomaly (Pp.str "Unnamed record variable.") in
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
        (Id.print fi ++
	   strbrk" cannot be defined because the projection" ++ str s ++ spc () ++
           prlist_with_sep pr_comma Id.print projs ++ spc () ++ str have ++
	   strbrk " not defined.")
    | BadTypedProj (fi,ctx,te) ->
	match te with
	  | ElimArity (_,_,_,_,Some (_,_,NonInformativeToInformative)) ->
              (Id.print fi ++
		strbrk" cannot be defined because it is informative and " ++
		Printer.pr_inductive (Global.env()) indsp ++
		strbrk " is not.")
	  | ElimArity (_,_,_,_,Some (_,_,StrongEliminationOnNonSmallType)) ->
	      (Id.print fi ++
		strbrk" cannot be defined because it is large and " ++
		Printer.pr_inductive (Global.env()) indsp ++
		strbrk " is not.")
	  | _ ->
              (Id.print fi ++ strbrk " cannot be defined because it is not typable.")
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
  let rec substrec depth c = match Constr.kind c with
    | Rel k ->
	(* We are in context [[params;fields;x:ind;...depth...]] *)
        if k <= depth+1 then
	  c
        else if k-depth-1 <= lv then
	  match List.nth l (k-depth-2) with
	    | Projection t -> lift depth t
	    | NoProjection (Name id) -> bad_projs := id :: !bad_projs; mkRel k
	    | NoProjection Anonymous ->
                user_err  (str "Field " ++ Id.print fid ++
                  str " depends on the " ++ pr_nth (k-depth-1) ++ str
                  " field which has no name.")
        else
	  mkRel (k-lv)
    | _ -> Constr.map_with_binders succ substrec depth c
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
let declare_projections indsp ctx ?(kind=StructureComponent) binder_name coers ubinders fieldimpls fields =
  let env = Global.env() in
  let (mib,mip) = Global.lookup_inductive indsp in
  let poly = Declareops.inductive_is_polymorphic mib in
  let u = match ctx with
    | Polymorphic_const_entry ctx -> Univ.UContext.instance ctx
    | Monomorphic_const_entry ctx -> Univ.Instance.empty
  in
  let paramdecls = Inductive.inductive_paramdecls (mib, u) in
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
                let gr = Nametab.locate (Libnames.qualid_of_ident fid) in
                let kn = destConstRef gr in
                Declare.definition_message fid;
                Universes.register_universe_binders gr ubinders;
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
                    const_entry_universes = ctx;
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
                  Universes.register_universe_binders (ConstRef kn) ubinders;
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

open Typeclasses

let declare_structure finite ubinders univs id idbuild paramimpls params arity template
    fieldimpls fields ?(kind=StructureComponent) ?name is_coe coers =
  let nparams = List.length params and nfields = List.length fields in
  let args = Context.Rel.to_extended_list mkRel nfields params in
  let ind = applist (mkRel (1+nparams+nfields), args) in
  let type_constructor = it_mkProd_or_LetIn ind fields in
  let template, ctx =
    match univs with
    | Monomorphic_ind_entry ctx ->
      template, Monomorphic_const_entry Univ.ContextSet.empty
    | Polymorphic_ind_entry ctx ->
      false, Polymorphic_const_entry ctx
    | Cumulative_ind_entry cumi ->
      false, Polymorphic_const_entry (Univ.CumulativityInfo.univ_context cumi)
  in
  let binder_name = 
    match name with
    | None -> Id.of_string (Unicode.lowercase_first_char (Id.to_string id)) 
    | Some n -> n
  in
  let mie_ind =
    { mind_entry_typename = id;
      mind_entry_arity = arity;
      mind_entry_template = template;
      mind_entry_consnames = [idbuild];
      mind_entry_lc = [type_constructor] }
  in
  let mie =
    { mind_entry_params = List.map degenerate_decl params;
      mind_entry_record = Some (if !primitive_flag then Some binder_name else None);
      mind_entry_finite = finite;
      mind_entry_inds = [mie_ind];
      mind_entry_private = None;
      mind_entry_universes = univs;
    }
  in
  let mie = InferCumulativity.infer_inductive (Global.env ()) mie in
  let kn = ComInductive.declare_mutual_inductive_with_eliminations mie ubinders [(paramimpls,[])] in
  let rsp = (kn,0) in (* This is ind path of idstruc *)
  let cstr = (rsp,1) in
  let kinds,sp_projs = declare_projections rsp ctx ~kind binder_name coers ubinders fieldimpls fields in
  let build = ConstructRef cstr in
  let poly = match ctx with | Polymorphic_const_entry _ -> true | Monomorphic_const_entry _ -> false in
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

let declare_class finite def cum ubinders univs id idbuild paramimpls params arity
    template fieldimpls fields ?(kind=StructureComponent) is_coe coers priorities =
  let fieldimpls =
    (* Make the class implicit in the projections, and the params if applicable. *)
    let len = List.length params in
    let impls = implicits_of_context params in
      List.map (fun x -> impls @ Impargs.lift_implicits (succ len) x) fieldimpls
  in
  let binder_name = Namegen.next_ident_away (snd id) (Termops.vars_of_env (Global.env())) in
  let impl, projs =
    match fields with
    | [LocalAssum (Name proj_name, field) | LocalDef (Name proj_name, _, field)] when def ->
      let class_body = it_mkLambda_or_LetIn field params in
      let class_type = it_mkProd_or_LetIn arity params in
      let class_entry = 
        Declare.definition_entry ~types:class_type ~univs class_body in
      let cst = Declare.declare_constant (snd id)
	(DefinitionEntry class_entry, IsDefinition Definition)
      in
      let cstu = (cst, match univs with
        | Polymorphic_const_entry univs -> Univ.UContext.instance univs
        | Monomorphic_const_entry _ -> Univ.Instance.empty)
      in
      let inst_type = appvectc (mkConstU cstu)
			       (Termops.rel_vect 0 (List.length params)) in
      let proj_type =
	it_mkProd_or_LetIn (mkProd(Name binder_name, inst_type, lift 1 field)) params in
      let proj_body =
	it_mkLambda_or_LetIn (mkLambda (Name binder_name, inst_type, mkRel 1)) params in
      let proj_entry = Declare.definition_entry ~types:proj_type ~univs proj_body in
      let proj_cst = Declare.declare_constant proj_name
        (DefinitionEntry proj_entry, IsDefinition Definition)
      in
      let cref = ConstRef cst in
      Impargs.declare_manual_implicits false cref [paramimpls];
      Universes.register_universe_binders cref ubinders;
      Impargs.declare_manual_implicits false (ConstRef proj_cst) [List.hd fieldimpls];
      Universes.register_universe_binders (ConstRef proj_cst) ubinders;
      Classes.set_typeclass_transparency (EvalConstRef cst) false false;
      let sub = match List.hd coers with
	| Some b -> Some ((if b then Backward else Forward), List.hd priorities) 
	| None -> None 
      in
      cref, [Name proj_name, sub, Some proj_cst]
    | _ ->
       let univs =
         match univs with
         | Polymorphic_const_entry univs ->
           if cum then
             Cumulative_ind_entry (Univ.CumulativityInfo.from_universe_context univs)
           else
             Polymorphic_ind_entry univs
         | Monomorphic_const_entry univs ->
           Monomorphic_ind_entry univs
       in
       let ind = declare_structure Declarations.BiFinite ubinders univs (snd id) idbuild paramimpls
	  params arity template fieldimpls fields
          ~kind:Method ~name:binder_name false (List.map (fun _ -> false) fields)
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
      | Some (_, ((cl,_), _)) -> Some cl.cl_impl
      | None -> None)
      params, params
  in
  let univs, ctx_context, fields =
    match univs with
    | Polymorphic_const_entry univs ->
      let usubst, auctx = Univ.abstract_universes univs in
      let usubst = Univ.make_instance_subst usubst in
      let map c = Vars.subst_univs_level_constr usubst c in
      let fields = Context.Rel.map map fields in
      let ctx_context = on_snd (fun d -> Context.Rel.map map d) ctx_context in
      auctx, ctx_context, fields
    | Monomorphic_const_entry _ ->
      Univ.AUContext.empty, ctx_context, fields
  in
  let k =
    { cl_univs = univs;
      cl_impl = impl;
      cl_strict = !typeclasses_strict;
      cl_unique = !typeclasses_unique;
      cl_context = ctx_context;
      cl_props = fields;
      cl_projs = projs }
  in
    add_class k; impl


let add_constant_class cst =
  let ty, univs = Global.type_of_global_in_context (Global.env ()) (ConstRef cst) in
  let ctx, arity = decompose_prod_assum ty in
  let tc = 
    { cl_univs = univs;
      cl_impl = ConstRef cst;
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
    let univs = Declareops.inductive_polymorphic_context mind in
    let env = push_context ~strict:false (Univ.AUContext.repr univs) (Global.env ()) in
    let env = push_rel_context ctx env in
    let inst = Univ.make_abstract_instance univs in
    let ty = Inductive.type_of_inductive env ((mind, oneind), inst) in
      { cl_univs = univs;
        cl_impl = IndRef ind;
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
let definition_structure (kind,cum,poly,finite,(is_coe,({CAst.loc;v=idstruc},pl)),ps,cfs,idbuild,s) =
  let cfs,notations = List.split cfs in
  let cfs,priorities = List.split cfs in
  let coers,fs = List.split cfs in
  let extract_name acc = function
      Vernacexpr.AssumExpr({CAst.v=Name id},_) -> id::acc
    | Vernacexpr.DefExpr ({CAst.v=Name id},_,_) -> id::acc
    | _ -> acc in
  let allnames =  idstruc::(List.fold_left extract_name [] fs) in
  let () = match List.duplicates Id.equal allnames with
  | [] -> ()
  | id :: _ -> user_err (str "Two objects have the same name" ++ spc () ++ quote (Id.print id))
  in
  let isnot_class = match kind with Class false -> false | _ -> true in
  if isnot_class && List.exists (fun opt -> not (Option.is_empty opt)) priorities then
    user_err Pp.(str "Priorities only allowed for type class substructures");
  (* Now, younger decl in params and fields is on top *)
  let pl, univs, arity, template, implpars, params, implfs, fields =
    States.with_state_protection (fun () ->
      typecheck_params_and_fields finite (kind = Class true) idstruc poly pl s ps notations fs) () in
  match kind with
  | Class def ->
    let priorities = List.map (fun id -> {hint_priority = id; hint_pattern = None}) priorities in
    declare_class finite def cum pl univs (loc,idstruc) idbuild
      implpars params arity template implfs fields is_coe coers priorities
  | _ ->
      let implfs = List.map
	  (fun impls -> implpars @ Impargs.lift_implicits
	           (succ (List.length params)) impls) implfs 
      in
      let univs =
        match univs with
        | Polymorphic_const_entry univs ->
          if cum then
            Cumulative_ind_entry (Univ.CumulativityInfo.from_universe_context univs)
          else
            Polymorphic_ind_entry univs
        | Monomorphic_const_entry univs ->
          Monomorphic_ind_entry univs
      in
      let ind = declare_structure finite pl univs idstruc
	  idbuild implpars params arity template implfs 
          fields is_coe (List.map (fun coe -> not (Option.is_empty coe)) coers) in
      IndRef ind
