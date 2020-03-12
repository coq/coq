(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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
open Nameops
open Constr
open Context
open Vars
open Environ
open Declarations
open Entries
open Declare
open Constrintern
open Type_errors
open Constrexpr
open Constrexpr_ops
open Goptions
open Context.Rel.Declaration
open Libobject

module RelDecl = Context.Rel.Declaration

(********** definition d'un record (structure) **************)

(** Flag governing use of primitive projections. Disabled by default. *)
let primitive_flag = ref false
let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Primitive";"Projections"];
      optread  = (fun () -> !primitive_flag) ;
      optwrite = (fun b -> primitive_flag := b) }

let typeclasses_strict = ref false
let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Typeclasses";"Strict";"Resolution"];
      optread  = (fun () -> !typeclasses_strict);
      optwrite = (fun b -> typeclasses_strict := b); }

let typeclasses_unique = ref false
let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Typeclasses";"Unique";"Instances"];
      optread  = (fun () -> !typeclasses_unique);
      optwrite = (fun b -> typeclasses_unique := b); }

let interp_fields_evars env sigma impls_env nots l =
  List.fold_left2
    (fun (env, sigma, uimpls, params, impls) no ({CAst.loc;v=i}, b, t) ->
      let sigma, (t', impl) = interp_type_evars_impls ~program_mode:false env sigma ~impls t in
      let r = Retyping.relevance_of_type env sigma t' in
      let sigma, b' =
        Option.cata (fun x -> on_snd (fun x -> Some (fst x)) @@
                      interp_casted_constr_evars_impls ~program_mode:false env sigma ~impls x t') (sigma,None) b in
      let impls =
        match i with
        | Anonymous -> impls
        | Name id -> Id.Map.add id (compute_internalization_data env sigma Constrintern.Method t' impl) impls
      in
      let d = match b' with
              | None -> LocalAssum (make_annot i r,t')
              | Some b' -> LocalDef (make_annot i r,b',t')
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
    l (env, Univ.Universe.sprop)

let binder_of_decl = function
  | Vernacexpr.AssumExpr(n,t) -> (n,None,t)
  | Vernacexpr.DefExpr(n,c,t) ->
    (n,Some c, match t with Some c -> c
                          | None   -> CAst.make ?loc:n.CAst.loc @@ CHole (None, Namegen.IntroAnonymous, None))

let binders_of_decls = List.map binder_of_decl

let check_anonymous_type ind =
  match ind with
  | { CAst.v = CSort (Glob_term.UAnonymous {rigid=true}) } -> true
  | _ -> false

let typecheck_params_and_fields finite def poly pl ps records =
  let env0 = Global.env () in
  (* Special case elaboration for template-polymorphic inductives,
     lower bound on introduced universes is Prop so that we do not miss
     any Set <= i constraint for universes that might actually be instantiated with Prop. *)
  let is_template =
    List.exists (fun (_, arity, _, _) -> Option.cata check_anonymous_type true arity) records in
  let env0 = if not poly && is_template then Environ.set_universes_lbound env0 Univ.Level.prop else env0 in
  let sigma, decl = Constrexpr_ops.interp_univ_decl_opt env0 pl in
  let () =
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
              Loc.raise ?loc (Stream.Error "pattern with quote not allowed in record parameters")) ps
  in
  let sigma, (impls_env, ((env1,newps), imps)) = interp_context_evars ~program_mode:false env0 sigma ps in
  let fold (sigma, template) (_, t, _, _) = match t with
    | Some t ->
       let env = EConstr.push_rel_context newps env0 in
       let poly =
         match t with
         | { CAst.v = CSort (Glob_term.UAnonymous {rigid=true}) } -> true | _ -> false in
       let sigma, s = interp_type_evars ~program_mode:false env sigma ~impls:empty_internalization_env t in
       let sred = Reductionops.whd_allnolet env sigma s in
         (match EConstr.kind sigma sred with
         | Sort s' ->
            let s' = EConstr.ESorts.kind sigma s' in
            (if poly then
               match Evd.is_sort_variable sigma s' with
               | Some l ->
                 let sigma = Evd.make_flexible_variable sigma ~algebraic:true l in
                 (sigma, template), (s, s')
               | None ->
                 (sigma, false), (s, s')
             else (sigma, false), (s, s'))
         | _ -> user_err ?loc:(constr_loc t) (str"Sort expected."))
    | None ->
      let uvarkind = Evd.univ_flexible_alg in
      let sigma, s = Evd.new_sort_variable uvarkind sigma in
      (sigma, template), (EConstr.mkSort s, s)
  in
  let (sigma, template), typs = List.fold_left_map fold (sigma, true) records in
  let arities = List.map (fun (typ, _) -> EConstr.it_mkProd_or_LetIn typ newps) typs in
  let relevances = List.map (fun (_,s) -> Sorts.relevance_of_sort s) typs in
  let fold accu (id, _, _, _) arity r =
    EConstr.push_rel (LocalAssum (make_annot (Name id) r,arity)) accu in
  let env_ar = EConstr.push_rel_context newps (List.fold_left3 fold env0 records arities relevances) in
  let assums = List.filter is_local_assum newps in
  let impls_env =
    let params = List.map (RelDecl.get_name %> Name.get_id) assums in
    let ty = Inductive (params, (finite != Declarations.BiFinite)) in
    let ids = List.map (fun (id, _, _, _) -> id) records in
    let imps = List.map (fun _ -> imps) arities in
    compute_internalization_env env0 sigma ~impls:impls_env ty ids arities imps
  in
  let fold sigma (_, _, nots, fs) arity =
    let _, sigma, impls, newfs, _ = interp_fields_evars env_ar sigma impls_env nots (binders_of_decls fs) in
    (sigma, (impls, newfs))
  in
  let (sigma, data) = List.fold_left2_map fold sigma records arities in
  let sigma =
    Pretyping.solve_remaining_evars Pretyping.all_and_fail_flags env_ar sigma in
  let fold sigma (typ, sort) (_, newfs) =
    let _, univ = compute_constructor_level sigma env_ar newfs in
    let univ = if Sorts.is_sprop sort then univ else Univ.Universe.sup univ Univ.type0m_univ in
      if not def && is_impredicative_sort env0 sort then
        sigma, (univ, typ)
      else
        let sigma = Evd.set_leq_sort env_ar sigma (Sorts.sort_of_univ univ) sort in
        if Univ.is_small_univ univ &&
           Option.cata (Evd.is_flexible_level sigma) false (Evd.is_sort_variable sigma sort) then
           (* We can assume that the level in aritysort is not constrained
               and clear it, if it is flexible *)
   Evd.set_eq_sort env_ar sigma Sorts.set sort, (univ, EConstr.mkSort (Sorts.sort_of_univ univ))
        else sigma, (univ, typ)
  in
  let (sigma, typs) = List.fold_left2_map fold sigma typs data in
  let sigma, (newps, ans) = Evarutil.finalize sigma (fun nf ->
      let newps = List.map (RelDecl.map_constr_het nf) newps in
      let map (impls, newfs) (univ, typ) =
        let newfs = List.map (RelDecl.map_constr_het nf) newfs in
        let typ = nf typ in
        (univ, typ, impls, newfs)
      in
      let ans = List.map2 map data typs in
      newps, ans)
  in
  let univs = Evd.check_univ_decl ~poly sigma decl in
  let ubinders = Evd.universe_binders sigma in
  let ce t = Pretyping.check_evars env0 sigma (EConstr.of_constr t) in
  let () = List.iter (iter_constr ce) (List.rev newps) in
  ubinders, univs, template, newps, imps, ans

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
          | ElimArity (_,_,_,Some (_,_,_,NonInformativeToInformative)) ->
              (Id.print fi ++
                strbrk" cannot be defined because it is informative and " ++
                Printer.pr_inductive (Global.env()) indsp ++
                strbrk " is not.")
          | ElimArity (_,_,_,Some (_,_,_,StrongEliminationOnNonSmallType)) ->
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

let instantiate_possibly_recursive_type ind u ntypes paramdecls fields =
  let subst = List.map_i (fun i _ -> mkRel i) 1 paramdecls in
  let subst' = List.init ntypes (fun i -> mkIndU ((ind, ntypes - i - 1), u)) in
  Termops.substl_rel_context (subst @ subst') fields

type projection_flags = {
  pf_subclass: bool;
  pf_canonical: bool;
}

(* We build projections *)
let declare_projections indsp ctx ?(kind=Decls.StructureComponent) binder_name flags fieldimpls fields =
  let env = Global.env() in
  let (mib,mip) = Global.lookup_inductive indsp in
  let poly = Declareops.inductive_is_polymorphic mib in
  let u = match ctx with
    | Polymorphic_entry (_, ctx) -> Univ.UContext.instance ctx
    | Monomorphic_entry ctx -> Univ.Instance.empty
  in
  let paramdecls = Inductive.inductive_paramdecls (mib, u) in
  let r = mkIndU (indsp,u) in
  let rp = applist (r, Context.Rel.to_extended_list mkRel 0 paramdecls) in
  let paramargs = Context.Rel.to_extended_list mkRel 1 paramdecls in (*def in [[params;x:rp]]*)
  let x = make_annot (Name binder_name) mip.mind_relevance in
  let fields = instantiate_possibly_recursive_type (fst indsp) u mib.mind_ntypes paramdecls fields in
  let lifted_fields = Termops.lift_rel_context 1 fields in
  let primitive =
    match mib.mind_record with
    | PrimRecord _ -> true
    | FakeRecord | NotRecord -> false
  in
  let (_,_,kinds,sp_projs,_) =
    List.fold_left3
      (fun (nfi,i,kinds,sp_projs,subst) flags decl impls ->
        let fi = RelDecl.get_name decl in
        let ti = RelDecl.get_type decl in
        let (sp_projs,i,subst) =
          match fi with
          | Anonymous ->
              (None::sp_projs,i,NoProjection fi::subst)
          | Name fid -> try
            let kn, term =
              if is_local_assum decl && primitive then
                let p = Projection.Repr.make indsp
                    ~proj_npars:mib.mind_nparams
                    ~proj_arg:i
                    (Label.of_id fid)
                in
                (* Already defined by declare_mind silently *)
                let kn = Projection.Repr.constant p in
                Declare.definition_message fid;
                kn, mkProj (Projection.make p false,mkRel 1)
              else
                let ccl = subst_projection fid subst ti in
                let body = match decl with
                  | LocalDef (_,ci,_) -> subst_projection fid subst ci
                  | LocalAssum ({binder_relevance=rci},_) ->
                    (* [ccl] is defined in context [params;x:rp] *)
                    (* [ccl'] is defined in context [params;x:rp;x:rp] *)
                    let ccl' = liftn 1 2 ccl in
                    let p = mkLambda (x, lift 1 rp, ccl') in
                    let branch = it_mkLambda_or_LetIn (mkRel nfi) lifted_fields in
                    let ci = Inductiveops.make_case_info env indsp rci LetStyle in
                    (* Record projections have no is *)
                    mkCase (ci, p, mkRel 1, [|branch|])
                in
                let proj =
                  it_mkLambda_or_LetIn (mkLambda (x,rp,body)) paramdecls in
                let projtyp =
                  it_mkProd_or_LetIn (mkProd (x,rp,ccl)) paramdecls in
                try
                  let entry = Declare.definition_entry ~univs:ctx ~types:projtyp proj in
                  let kind = Decls.IsDefinition kind in
                  let kn = declare_constant ~name:fid ~kind (Declare.DefinitionEntry entry) in
                  let constr_fip =
                    let proj_args = (*Rel 1 refers to "x"*) paramargs@[mkRel 1] in
                      applist (mkConstU (kn,u),proj_args)
                  in
                  Declare.definition_message fid;
                    kn, constr_fip
                with Type_errors.TypeError (ctx,te) ->
                  raise (NotDefinable (BadTypedProj (fid,ctx,te)))
            in
            let refi = GlobRef.ConstRef kn in
            Impargs.maybe_declare_manual_implicits false refi impls;
            if flags.pf_subclass then begin
              let cl = ComCoercion.class_of_global (GlobRef.IndRef indsp) in
                ComCoercion.try_add_new_coercion_with_source refi ~local:false ~poly ~source:cl
            end;
            let i = if is_local_assum decl then i+1 else i in
              (Some kn::sp_projs, i, Projection term::subst)
            with NotDefinable why ->
              warning_or_error flags.pf_subclass indsp why;
              (None::sp_projs,i,NoProjection fi::subst) in
      (nfi - 1, i, { Recordops.pk_name = fi ; pk_true_proj = is_local_assum decl ; pk_canonical = flags.pf_canonical } :: kinds, sp_projs, subst))
      (List.length fields,0,[],[],[]) flags (List.rev fields) (List.rev fieldimpls)
  in (kinds,sp_projs)

open Typeclasses

let load_structure i (_, structure) =
  Recordops.register_structure (Global.env()) structure

let cache_structure o =
  load_structure 1 o

let subst_structure (subst, (id, kl, projs as obj)) =
  Recordops.subst_structure subst obj

let discharge_structure (_, x) = Some x

let inStruc : Recordops.struc_tuple -> obj =
  declare_object {(default_object "STRUCTURE") with
    cache_function = cache_structure;
    load_function = load_structure;
    subst_function = subst_structure;
    classify_function = (fun x -> Substitute x);
    discharge_function = discharge_structure }

let declare_structure_entry o =
  Lib.add_anonymous_leaf (inStruc o)

let declare_structure ~cumulative finite ubinders univs paramimpls params template ?(kind=Decls.StructureComponent) ?name record_data =
  let nparams = List.length params in
  let poly, ctx =
    match univs with
    | Monomorphic_entry ctx ->
      false, Monomorphic_entry Univ.ContextSet.empty
    | Polymorphic_entry (nas, ctx) ->
      true, Polymorphic_entry (nas, ctx)
  in
  let binder_name =
    match name with
    | None ->
      let map (id, _, _, _, _, _, _, _) =
        Id.of_string (Unicode.lowercase_first_char (Id.to_string id))
      in
      Array.map_of_list map record_data
    | Some n -> n
  in
  let ntypes = List.length record_data in
  let mk_block i (id, idbuild, min_univ, arity, _, fields, _, _) =
    let nfields = List.length fields in
    let args = Context.Rel.to_extended_list mkRel nfields params in
    let ind = applist (mkRel (ntypes - i + nparams + nfields), args) in
    let type_constructor = it_mkProd_or_LetIn ind fields in
    { mind_entry_typename = id;
      mind_entry_arity = arity;
      mind_entry_consnames = [idbuild];
      mind_entry_lc = [type_constructor] }
  in
  let blocks = List.mapi mk_block record_data in
  let check_template (id, _, min_univ, _, _, fields, _, _) =
      let template_candidate () =
        (* we use some dummy values for the arities in the rel_context
           as univs_of_constr doesn't care about localassums and
           getting the real values is too annoying *)
        let add_levels c levels = Univ.LSet.union levels (Vars.universes_of_constr c) in
        let param_levels =
          List.fold_left (fun levels d -> match d with
              | LocalAssum _ -> levels
              | LocalDef (_,b,t) -> add_levels b (add_levels t levels))
            Univ.LSet.empty params
        in
        let ctor_levels = List.fold_left
            (fun univs d ->
               let univs =
                 RelDecl.fold_constr (fun c univs -> add_levels c univs) d univs
               in
               univs)
            param_levels fields
        in
        ComInductive.template_polymorphism_candidate ~ctor_levels univs params
          (Some (Sorts.sort_of_univ min_univ))
      in
      match template with
      | Some template, _ ->
        (* templateness explicitly requested *)
        if poly && template then user_err Pp.(strbrk "template and polymorphism not compatible");
        template
      | None, template ->
        (* auto detect template *)
        ComInductive.should_auto_template id (template && template_candidate ())
  in
  let template = List.for_all check_template record_data in
  let primitive =
    !primitive_flag &&
    List.for_all (fun (_,_,_,_,_,fields,_,_) -> List.exists is_local_assum fields) record_data
  in
  let mie =
    { mind_entry_params = params;
      mind_entry_record = Some (if primitive then Some binder_name else None);
      mind_entry_finite = finite;
      mind_entry_inds = blocks;
      mind_entry_private = None;
      mind_entry_universes = univs;
      mind_entry_template = template;
      mind_entry_cumulative = poly && cumulative;
    }
  in
  let impls = List.map (fun _ -> paramimpls, []) record_data in
  let kn = DeclareInd.declare_mutual_inductive_with_eliminations mie ubinders impls
      ~primitive_expected:!primitive_flag
  in
  let map i (_, _, _, _, fieldimpls, fields, is_coe, coers) =
    let rsp = (kn, i) in (* This is ind path of idstruc *)
    let cstr = (rsp, 1) in
    let kinds,sp_projs = declare_projections rsp ctx ~kind binder_name.(i) coers fieldimpls fields in
    let build = GlobRef.ConstructRef cstr in
    let () = if is_coe then ComCoercion.try_add_new_coercion build ~local:false ~poly in
    let () = declare_structure_entry (cstr, List.rev kinds, List.rev sp_projs) in
    rsp
  in
  List.mapi map record_data

let implicits_of_context ctx =
  List.map (fun name -> CAst.make (Some (name,true)))
    (List.rev (Anonymous :: (List.map RelDecl.get_name ctx)))

let declare_class def cumulative ubinders univs id idbuild paramimpls params univ arity
    template fieldimpls fields ?(kind=Decls.StructureComponent) coers priorities =
  let fieldimpls =
    (* Make the class implicit in the projections, and the params if applicable. *)
    let impls = implicits_of_context params in
      List.map (fun x -> impls @ x) fieldimpls
  in
  let binder_name = Namegen.next_ident_away id (Termops.vars_of_env (Global.env())) in
  let data =
    match fields with
    | [LocalAssum ({binder_name=Name proj_name} as binder, field)
      | LocalDef ({binder_name=Name proj_name} as binder, _, field)] when def ->
      let binder = {binder with binder_name=Name binder_name} in
      let class_body = it_mkLambda_or_LetIn field params in
      let class_type = it_mkProd_or_LetIn arity params in
      let class_entry =
        Declare.definition_entry ~types:class_type ~univs class_body in
      let cst = Declare.declare_constant ~name:id
        (DefinitionEntry class_entry) ~kind:Decls.(IsDefinition Definition)
      in
      let inst, univs = match univs with
        | Polymorphic_entry (_, uctx) -> Univ.UContext.instance uctx, univs
        | Monomorphic_entry _ -> Univ.Instance.empty, Monomorphic_entry Univ.ContextSet.empty
      in
      let cstu = (cst, inst) in
      let inst_type = appvectc (mkConstU cstu)
          (Termops.rel_vect 0 (List.length params)) in
      let proj_type =
        it_mkProd_or_LetIn (mkProd(binder, inst_type, lift 1 field)) params in
      let proj_body =
        it_mkLambda_or_LetIn (mkLambda (binder, inst_type, mkRel 1)) params in
      let proj_entry = Declare.definition_entry ~types:proj_type ~univs proj_body in
      let proj_cst = Declare.declare_constant ~name:proj_name
        (DefinitionEntry proj_entry) ~kind:Decls.(IsDefinition Definition)
      in
      let cref = GlobRef.ConstRef cst in
      Impargs.declare_manual_implicits false cref paramimpls;
      Impargs.declare_manual_implicits false (GlobRef.ConstRef proj_cst) (List.hd fieldimpls);
      Classes.set_typeclass_transparency (EvalConstRef cst) false false;
      let sub = match List.hd coers with
        | Some b -> Some ((if b then Backward else Forward), List.hd priorities)
        | None -> None
      in
      [cref, [Name proj_name, sub, Some proj_cst]]
    | _ ->
      let record_data = [id, idbuild, univ, arity, fieldimpls, fields, false,
                         List.map (fun _ -> { pf_subclass = false ; pf_canonical = true }) fields] in
      let inds = declare_structure ~cumulative Declarations.BiFinite ubinders univs paramimpls
        params template ~kind:Decls.Method ~name:[|binder_name|] record_data
      in
       let coers = List.map2 (fun coe pri ->
                              Option.map (fun b ->
                              if b then Backward, pri else Forward, pri) coe)
          coers priorities
       in
      let map ind =
        let l = List.map3 (fun decl b y -> RelDecl.get_name decl, b, y)
          (List.rev fields) coers (Recordops.lookup_projections ind)
        in GlobRef.IndRef ind, l
      in
      List.map map inds
  in
  let ctx_context =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    List.map (fun decl ->
      match Typeclasses.class_of_constr env sigma (EConstr.of_constr (RelDecl.get_type decl)) with
      | Some (_, ((cl,_), _)) -> Some cl.cl_impl
      | None -> None)
      params, params
  in
  let univs, ctx_context, fields =
    match univs with
    | Polymorphic_entry (nas, univs) ->
      let usubst, auctx = Univ.abstract_universes nas univs in
      let usubst = Univ.make_instance_subst usubst in
      let map c = Vars.subst_univs_level_constr usubst c in
      let fields = Context.Rel.map map fields in
      let ctx_context = on_snd (fun d -> Context.Rel.map map d) ctx_context in
      auctx, ctx_context, fields
    | Monomorphic_entry _ ->
      Univ.AUContext.empty, ctx_context, fields
  in
  let map (impl, projs) =
    let k =
      { cl_univs = univs;
        cl_impl = impl;
        cl_strict = !typeclasses_strict;
        cl_unique = !typeclasses_unique;
        cl_context = ctx_context;
        cl_props = fields;
        cl_projs = projs }
    in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    Classes.add_class env sigma k; impl
  in
  List.map map data


let add_constant_class env sigma cst =
  let ty, univs = Typeops.type_of_global_in_context env (GlobRef.ConstRef cst) in
  let r = (Environ.lookup_constant cst env).const_relevance in
  let ctx, _ = decompose_prod_assum ty in
  let args = Context.Rel.to_extended_vect Constr.mkRel 0 ctx in
  let t = mkApp (mkConstU (cst, Univ.make_abstract_instance univs), args) in
  let tc =
    { cl_univs = univs;
      cl_impl = GlobRef.ConstRef cst;
      cl_context = (List.map (const None) ctx, ctx);
      cl_props = [LocalAssum (make_annot Anonymous r, t)];
      cl_projs = [];
      cl_strict = !typeclasses_strict;
      cl_unique = !typeclasses_unique
    }
  in
  Classes.add_class env sigma tc;
    Classes.set_typeclass_transparency (EvalConstRef cst) false false

let add_inductive_class env sigma ind =
  let mind, oneind = Inductive.lookup_mind_specif env ind in
  let k =
    let ctx = oneind.mind_arity_ctxt in
    let univs = Declareops.inductive_polymorphic_context mind in
    let env = push_context ~strict:false (Univ.AUContext.repr univs) env in
    let env = push_rel_context ctx env in
    let inst = Univ.make_abstract_instance univs in
    let ty = Inductive.type_of_inductive ((mind, oneind), inst) in
    let r = Inductive.relevance_of_inductive env ind in
      { cl_univs = univs;
        cl_impl = GlobRef.IndRef ind;
        cl_context = List.map (const None) ctx, ctx;
        cl_props = [LocalAssum (make_annot Anonymous r, ty)];
        cl_projs = [];
        cl_strict = !typeclasses_strict;
        cl_unique = !typeclasses_unique }
  in
  Classes.add_class env sigma k

let warn_already_existing_class =
  CWarnings.create ~name:"already-existing-class" ~category:"automation" Pp.(fun g ->
      Printer.pr_global g ++ str " is already declared as a typeclass.")

let declare_existing_class g =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  if Typeclasses.is_class g then warn_already_existing_class g
  else
    match g with
    | GlobRef.ConstRef x -> add_constant_class env sigma x
    | GlobRef.IndRef x -> add_inductive_class env sigma x
    | _ -> user_err ~hdr:"declare_existing_class"
             (Pp.str"Unsupported class type, only constants and inductives are allowed")

open Vernacexpr

let check_unique_names records =
  let extract_name acc (rf_decl, _) = match rf_decl with
      Vernacexpr.AssumExpr({CAst.v=Name id},_) -> id::acc
    | Vernacexpr.DefExpr ({CAst.v=Name id},_,_) -> id::acc
    | _ -> acc in
  let allnames =
    List.fold_left (fun acc (_, id, _, cfs, _, _) ->
      id.CAst.v :: (List.fold_left extract_name acc cfs)) [] records
  in
  match List.duplicates Id.equal allnames with
  | [] -> ()
  | id :: _ -> user_err (str "Two objects have the same name" ++ spc () ++ quote (Id.print id))

let check_priorities kind records =
  let isnot_class = match kind with Class false -> false | _ -> true in
  let has_priority (_, _, _, cfs, _, _) =
    List.exists (fun (_, { rf_priority }) -> not (Option.is_empty rf_priority)) cfs
  in
  if isnot_class && List.exists has_priority records then
    user_err Pp.(str "Priorities only allowed for type class substructures")

let extract_record_data records =
  let map (is_coe, id, _, cfs, idbuild, s) =
    let fs = List.map fst cfs in
    id.CAst.v, s, List.map (fun (_, { rf_notation }) -> rf_notation) cfs, fs
  in
  let data = List.map map records in
  let pss = List.map (fun (_, _, ps, _, _, _) -> ps) records in
  let ps = match pss with
  | [] -> CErrors.anomaly (str "Empty record block")
  | ps :: rem ->
    let eq_local_binders bl1 bl2 = List.equal local_binder_eq bl1 bl2 in
    let () =
      if not (List.for_all (eq_local_binders ps) rem) then
        user_err (str "Parameters should be syntactically the \
          same for each inductive type.")
    in
    ps
  in
  ps, data

(* [fs] corresponds to fields and [ps] to parameters; [coers] is a
   list telling if the corresponding fields must me declared as coercions
   or subinstances. *)
let definition_structure udecl kind ~template ~cumulative ~poly finite records =
  let () = check_unique_names records in
  let () = check_priorities kind records in
  let ps, data = extract_record_data records in
  let ubinders, univs, auto_template, params, implpars, data =
    States.with_state_protection (fun () ->
      typecheck_params_and_fields finite (kind = Class true) poly udecl ps data) () in
  let template = template, auto_template in
  match kind with
  | Class def ->
    let (_, id, _, cfs, idbuild, _), (univ, arity, implfs, fields) = match records, data with
    | [r], [d] -> r, d
    | _, _ -> CErrors.user_err (str "Mutual definitional classes are not handled")
    in
    let priorities = List.map (fun (_, { rf_priority }) -> {hint_priority = rf_priority ; hint_pattern = None}) cfs in
    let coers = List.map (fun (_, { rf_subclass }) -> rf_subclass) cfs in
    declare_class def cumulative ubinders univs id.CAst.v idbuild
      implpars params univ arity template implfs fields coers priorities
  | _ ->
    let map impls = implpars @ [CAst.make None] @ impls in
    let data = List.map (fun (univ, arity, implfs, fields) -> (univ, arity, List.map map implfs, fields)) data in
    let map (univ, arity, implfs, fields) (is_coe, id, _, cfs, idbuild, _) =
      let coe = List.map (fun (_, { rf_subclass ; rf_canonical }) ->
          { pf_subclass = not (Option.is_empty rf_subclass);
            pf_canonical = rf_canonical })
          cfs
      in
      id.CAst.v, idbuild, univ, arity, implfs, fields, is_coe, coe
    in
    let data = List.map2 map data records in
    let inds = declare_structure ~cumulative finite ubinders univs implpars params template data in
    List.map (fun ind -> GlobRef.IndRef ind) inds
