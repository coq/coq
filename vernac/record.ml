(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Term
open Util
open Names
open Constr
open Context
open Environ
open Declarations
open Entries
open Type_errors
open Constrexpr
open Constrexpr_ops
open Context.Rel.Declaration
open Structures

module RelDecl = Context.Rel.Declaration

(********** definition d'un record (structure) **************)

let { Goptions.get = typeclasses_strict } =
  Goptions.declare_bool_option_and_ref
    ~key:["Typeclasses";"Strict";"Resolution"]
    ~value:false
    ()

let { Goptions.get = typeclasses_unique } =
  Goptions.declare_bool_option_and_ref
    ~key:["Typeclasses";"Unique";"Instances"]
    ~value:false
    ()

let { Goptions.get = typeclasses_default_mode } =
  Goptions.declare_interpreted_string_option_and_ref Hints.parse_mode Hints.string_of_mode
    ~key:["Typeclasses";"Default";"Mode"]
    ~value:Hints.ModeOutput
    ()

let interp_fields_evars env sigma ~ninds ~nparams impls_env nots l =
  let _, sigma, impls, newfs, _ =
    List.fold_left2
      (fun (env, sigma, uimpls, params, impls_env) no d ->
         let sigma, (i, b, t), impl = match d with
           | Vernacexpr.AssumExpr({CAst.v=id},bl,t) ->
             (* Temporary compatibility with the type-classes heuristics *)
             (* which are applied after the interpretation of bl and *)
             (* before the one of t otherwise (see #13166) *)
             let t = if bl = [] then t else mkCProdN bl t in
             let sigma, t, impl =
               ComAssumption.interp_assumption ~program_mode:false env sigma impls_env [] t in
             sigma, (id, None, t), impl
           | Vernacexpr.DefExpr({CAst.v=id},bl,b,t) ->
             let sigma, (b, t), impl =
               ComDefinition.interp_definition ~program_mode:false env sigma impls_env bl None b t in
             let t = match t with Some t -> t | None -> Retyping.get_type_of env sigma b in
             sigma, (id, Some b, t), impl in
          let r = Retyping.relevance_of_type env sigma t in
         let impls_env =
           match i with
           | Anonymous -> impls_env
           | Name id ->
             Id.Map.add id (Constrintern.compute_internalization_data env sigma id Constrintern.Method t impl) impls_env
         in
         let d = match b with
           | None -> LocalAssum (make_annot i r,t)
           | Some b -> LocalDef (make_annot i r,b,t)
         in
         List.iter (Metasyntax.set_notation_for_interpretation env impls_env) no;
         (EConstr.push_rel d env, sigma, impl :: uimpls, d::params, impls_env))
      (env, sigma, [], [], impls_env) nots l
  in
  let _, _, sigma = Context.Rel.fold_outside ~init:(env,0,sigma) (fun f (env,k,sigma) ->
      let sigma = RelDecl.fold_constr (fun c sigma ->
          ComInductive.maybe_unify_params_in env sigma ~ninds ~nparams ~binders:k c)
          f sigma
      in
      EConstr.push_rel f env, k+1, sigma)
      newfs
  in
  sigma, (impls, newfs)

let check_anonymous_type ind =
  match ind with
  | { CAst.v = CSort s } -> Constrexpr_ops.(sort_expr_eq (expr_Type_sort UState.univ_flexible) s)
  | _ -> false

let error_parameters_must_be_named bk {CAst.loc; v=name} =
  match bk, name with
  | Default _, Anonymous ->
    CErrors.user_err ?loc (str "Record parameters must be named.")
  | _ -> ()

let check_parameters_must_be_named = function
  | CLocalDef (b, _, _, _) ->
    error_parameters_must_be_named default_binder_kind b
  | CLocalAssum (ls, _, bk, _ce) ->
    List.iter (error_parameters_must_be_named bk) ls
  | CLocalPattern {CAst.loc} ->
    Loc.raise ?loc (Gramlib.Grammar.Error "pattern with quote not allowed in record parameters")

(** [DataI.t] contains the information used in record interpretation,
   it is a strict subset of [Ast.t] thus this should be
   eventually removed or merged with [Ast.t] *)
module DataI = struct
  type t =
    { name : Id.t
    ; arity : Constrexpr.constr_expr option
    (** declared sort for the record  *)
    ; nots : Metasyntax.notation_interpretation_decl list list
    (** notations for fields *)
    ; fs : Vernacexpr.local_decl_expr list
    }
end

(** [DataR.t] contains record data after interpretation /
   type-inference *)
module DataR = struct
  type t =
    { arity : Constr.t
    ; default_dep_elim : DeclareInd.default_dep_elim
    ; implfs : Impargs.manual_implicits list
    ; fields : Constr.rel_declaration list
    }
end

module Data = struct
  type projection_flags = {
    pf_coercion: bool;
    pf_reversible: bool;
    pf_instance: bool;
    pf_priority: int option;
    pf_locality: Goptions.option_locality;
    pf_canonical: bool;
  }
  type raw_data = DataR.t
  type t =
  { id : Id.t
  ; idbuild : Id.t
  ; is_coercion : bool
  ; proj_flags : projection_flags list
  ; rdata : raw_data
  ; inhabitant_id : Id.t
  }
end

(** Is [s] a single local level (type or qsort)? If so return it. *)
let is_sort_variable sigma s =
  match EConstr.ESorts.kind sigma s with
  | SProp | Prop | Set -> None
  | Type u | QSort (_, u) -> match Univ.Universe.level u with
    | None -> None
    | Some l ->
      if Univ.Level.Set.mem l (fst (Evd.universe_context_set sigma))
      then Some l
      else None

let build_type_telescope ~unconstrained_sorts newps env0 sigma { DataI.arity; _ } = match arity with
  | None ->
    let sigma, s = Evd.new_sort_variable Evd.univ_flexible sigma in
    sigma, (EConstr.mkSort s, s)
  | Some { CAst.v = CSort s; loc } when Constrexpr_ops.(sort_expr_eq (expr_Type_sort UState.univ_flexible) s) ->
    (* special case: the user wrote ": Type". We want to allow it to become algebraic
       (and Prop but that may change in the future) *)
    let sigma, s = Evd.new_sort_variable ?loc UState.univ_flexible sigma in
    sigma, (EConstr.mkSort s, s)
  | Some t ->
    let env = EConstr.push_rel_context newps env0 in
    let impls = Constrintern.empty_internalization_env in
    let sigma, s =
      let t = Constrintern.intern_gen IsType ~impls env sigma t in
      let flags = { Pretyping.all_no_fail_flags with program_mode = false; unconstrained_sorts } in
      Pretyping.understand_tcc ~flags env sigma ~expected_type:IsType t
    in
    let sred = Reductionops.whd_allnolet env sigma s in
    (match EConstr.kind sigma sred with
     | Sort s' -> (sigma, (s, s'))
     | _ -> user_err ?loc:(constr_loc t) (str"Sort expected."))

type tc_result =
  Impargs.manual_implicits
  (* Part relative to closing the definitions *)
  * UState.named_universes_entry
  * Constr.rel_context
  * DataR.t list

(* returned DefaultElim value will eventually be discarded *)
let def_class_levels ~def env_ar sigma aritysorts ctors =
  let s, ctor = match aritysorts, ctors with
    | [s], [_,ctor] -> begin match ctor with
        | [LocalAssum (_,t)] -> s, t
        | _ -> assert false
      end
    | _ -> CErrors.user_err Pp.(str "Mutual definitional classes are not supported.")
  in
  let ctor_sort = Retyping.get_sort_of env_ar sigma ctor in
  let is_prop_ctor = EConstr.ESorts.is_prop sigma ctor_sort in
  let sigma = Evd.set_leq_sort env_ar sigma ctor_sort s in
  if Option.cata (Evd.is_flexible_level sigma) false (is_sort_variable sigma s)
  && is_prop_ctor
  then (* We assume that the level in aritysort is not constrained
          and clear it, if it is flexible *)
    let sigma = Evd.set_eq_sort env_ar sigma EConstr.ESorts.set s in
    (sigma, [DeclareInd.DefaultElim, EConstr.mkProp])
  else
    sigma, [DefaultElim, EConstr.mkSort s]

(* ps = parameter list *)
let typecheck_params_and_fields ~auto_prop_lowering def ~poly ~cumulative udecl ps (records : DataI.t list) : tc_result =
  let env0 = Global.env () in
  (* Special case elaboration for template-polymorphic inductives,
     lower bound on introduced universes is Prop so that we do not miss
     any Set <= i constraint for universes that might actually be instantiated with Prop. *)
  let is_template =
    List.exists (fun { DataI.arity; _} -> Option.cata check_anonymous_type true arity) records in
  let unconstrained_sorts = not poly && not def && is_template in
  let sigma, decl = Constrintern.interp_cumul_univ_decl_opt env0 udecl in
  let () = List.iter check_parameters_must_be_named ps in
  let sigma, (impls_env, ((_env1,newps), imps)) =
    Constrintern.interp_context_evars ~program_mode:false ~unconstrained_sorts env0 sigma ps in
  let sigma, typs =
    List.fold_left_map (build_type_telescope ~unconstrained_sorts newps env0) sigma records in
  let typs, aritysorts = List.split typs in
  let arities = List.map (fun typ -> EConstr.it_mkProd_or_LetIn typ newps) typs in
  let relevances = List.map (fun s -> EConstr.ESorts.relevance_of_sort s) aritysorts in
  let fold accu { DataI.name; _ } arity r =
    EConstr.push_rel (LocalAssum (make_annot (Name name) r,arity)) accu in
  let env_ar = EConstr.push_rel_context newps (List.fold_left3 fold env0 records arities relevances) in
  let impls_env =
    let ids = List.map (fun { DataI.name; _ } -> name) records in
    let imps = List.map (fun _ -> imps) arities in
    Constrintern.compute_internalization_env env0 sigma ~impls:impls_env Constrintern.Inductive ids arities imps
  in
  let ninds = List.length arities in
  let nparams = List.length newps in
  let fold sigma { DataI.nots; fs; _ } =
    interp_fields_evars env_ar sigma ~ninds ~nparams impls_env nots fs
  in
  let (sigma, data) = List.fold_left_map fold sigma records in
  let sigma =
    Pretyping.solve_remaining_evars Pretyping.all_and_fail_flags env_ar sigma in
  let sigma, typs =
    if def then def_class_levels ~def env_ar sigma aritysorts data
    else (* each inductive has one constructor *)
      let ctors = List.map (fun (_,newfs) -> [newfs]) data in
      let indnames = List.map (fun x -> x.DataI.name) records in
      let arities_explicit = List.map (fun x -> Option.has_some x.DataI.arity) records in
      let sigma, (default_dep_elim, typs) =
        ComInductive.Internal.inductive_levels ~auto_prop_lowering env_ar sigma ~poly ~indnames ~arities_explicit typs ctors
      in
      sigma, List.combine default_dep_elim typs
  in
  (* TODO: Have this use Declaredef.prepare_definition *)
  let lbound = if unconstrained_sorts then UGraph.Bound.Prop else UGraph.Bound.Set in
  let sigma = UnivVariances.register_universe_variances_of_record env0 sigma ~env_ar_pars:env_ar ~params:newps ~fields:(List.map snd data) ~types:(List.map snd typs) in
  let sigma, (newps, ans) =
    (* too complex for Evarutil.finalize as we normalize non-constr *)
    let sigma = Evd.minimize_universes ~lbound sigma in
    let uvars = ref Univ.Level.Set.empty in
    let nf c =
      let _, varsc = EConstr.universes_of_constr sigma c in
      let c = EConstr.to_constr sigma c in
      uvars := Univ.Level.Set.union !uvars varsc;
      c
    in
    let nf_rel r = EConstr.ERelevance.kind sigma r in
    let map_decl = RelDecl.map_constr_het nf_rel nf in
    let newps = List.map map_decl newps in
    let map (implfs, fields) (default_dep_elim, typ) =
      let fields = List.map map_decl fields in
      let arity = nf typ in
      { DataR.arity; default_dep_elim; implfs; fields }
    in
    let ans = List.map2 map data typs in
    let sigma = Evd.restrict_universe_context ~lbound sigma !uvars in
    sigma, (newps, ans)
  in
  let univs = Evd.check_univ_decl ~poly ~cumulative sigma decl in
  let ce t = Pretyping.check_evars env0 sigma (EConstr.of_constr t) in
  let () = List.iter (iter_constr ce) (List.rev newps) in
  imps, univs, newps, ans

type record_error =
  | MissingProj of Id.t * Id.t list
  | BadTypedProj of Id.t * env * Type_errors.type_error

let warn_cannot_define_projection =
  CWarnings.create ~name:"cannot-define-projection" ~category:CWarnings.CoreCategories.records
         (fun msg -> hov 0 msg)

type arity_error =
  | NonInformativeToInformative
  | StrongEliminationOnNonSmallType

let error_elim_explain kp ki =
  let open Sorts in
  match kp,ki with
  | (InType | InSet), InProp -> Some NonInformativeToInformative
  | InType, InSet -> Some StrongEliminationOnNonSmallType (* if Set impredicative *)
  | _ -> None

(* If a projection is not definable, we throw an error if the user
asked it to be a coercion or instance. Otherwise, we just print an info
message. The user might still want to name the field of the record. *)
let warning_or_error ~info flags indsp err =
  let st = match err with
    | MissingProj (fi,projs) ->
        let s,have = if List.length projs > 1 then "s","were" else "","was" in
        (Id.print fi ++
           strbrk" cannot be defined because the projection" ++ str s ++ spc () ++
           prlist_with_sep pr_comma Id.print projs ++ spc () ++ str have ++
           strbrk " not defined.")
    | BadTypedProj (fi,env,te) ->
      let err = match te with
        | ElimArity (_, _, Some s) ->
          error_elim_explain (Sorts.family s)
            (Inductiveops.elim_sort (Global.lookup_inductive indsp))
        | _ -> None
      in
        match err with
          | Some NonInformativeToInformative ->
              (Id.print fi ++
                strbrk" cannot be defined because it is informative and " ++
                Printer.pr_inductive (Global.env()) indsp ++
                strbrk " is not.")
          | Some StrongEliminationOnNonSmallType ->
              (Id.print fi ++
                strbrk" cannot be defined because it is large and " ++
                Printer.pr_inductive (Global.env()) indsp ++
                strbrk " is not.")
          | None ->
            (Id.print fi ++ str " cannot be defined because it is not typable:" ++ spc() ++
             Himsg.explain_type_error env (Evd.from_env env)
               (Pretype_errors.of_type_error te))
  in
  if flags.Data.pf_coercion || flags.Data.pf_instance then user_err ~info st;
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
  Vars.substl_rel_context (subst @ subst') fields

(* We build projections *)

(** Declare projection [ref] over [from] a coercion
   or a typeclass instance according to [flags]. *)
let declare_proj_coercion_instance ~flags ref from =
  if flags.Data.pf_coercion then begin
    let cl = ComCoercion.class_of_global from in
    let local = flags.Data.pf_locality = Goptions.OptLocal in
    ComCoercion.try_add_new_coercion_with_source ref ~local ~reversible:flags.Data.pf_reversible ~source:cl
  end;
  if flags.Data.pf_instance then begin
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let info = Typeclasses.{ hint_priority = flags.Data.pf_priority; hint_pattern = None } in
    let local =
      match flags.Data.pf_locality with
      | Goptions.OptLocal -> Hints.Local
      | Goptions.(OptDefault | OptExport) -> Hints.Export
      | Goptions.OptGlobal -> Hints.SuperGlobal in
    Classes.declare_instance ~warn:true env sigma (Some info) local ref
  end

let make_projection_variances i variances =
  match variances with
  | None -> None
  | Some v ->
    let open UVars in
    let arr = UVars.Variances.repr v in
    let map occ =
      match VarianceOccurrence.term_variance_pos occ with
      | (_, InBinder _) -> { occ with in_type = None } (* A parameter universe of the record, appearing in a parameter binder *)
      | (_, InType) -> (* A universe appearing only in the type of the record, we don't care *)
        occ
      | (var, InTerm) -> (* The universe appears in the type of a field of the record,
          and possibly in a binder as well.
          it can only appear in the binder for the record itself in a projection *)
        let open UVars.Variance in
        let ovar = match var with
          | Covariant -> Contravariant
          | Contravariant -> Covariant
          | Invariant -> Invariant
          | Irrelevant -> Irrelevant
        in
        { in_binders = List.append occ.in_binders [(i, ovar)]; in_term = Some var; in_type = Some var }
    in
    Some (UVars.Variances.make (Array.map map arr))

(* TODO: refactor the declaration part here; this requires some
   surgery as Evarutil.finalize is called too early in the path *)
(** This builds and _declares_ a named projection, the code looks
   tricky due to the term manipulation. It also handles declaring the
   implicits parameters, coercion status, etc... of the projection;
   this could be refactored as noted above by moving to the
   higher-level declare constant API *)
let build_named_proj ~primitive ~flags ~poly ~univs ~uinstance ~kind env paramdecls
    paramargs decl impls fid subst nfi ti i indsp mib lifted_fields x rp =
  let ccl = subst_projection fid subst ti in
  let body, p_opt = match decl with
    | LocalDef (_,ci,_) -> subst_projection fid subst ci, None
    | LocalAssum ({binder_relevance=rci},_) ->
      (* [ccl] is defined in context [params;x:rp] *)
      (* [ccl'] is defined in context [params;x:rp;x:rp] *)
      if primitive then
        let p = Projection.Repr.make indsp
            ~proj_npars:mib.mind_nparams ~proj_arg:i (Label.of_id fid) in
        mkProj (Projection.make p false, rci, mkRel 1), Some (p,rci)
      else
        let ccl' = liftn 1 2 ccl in
        let p = mkLambda (x, lift 1 rp, ccl') in
        let branch = it_mkLambda_or_LetIn (mkRel nfi) lifted_fields in
        let ci = Inductiveops.make_case_info env indsp LetStyle in
        (* Record projections are always NoInvert because they're at
           constant relevance *)
        mkCase (Inductive.contract_case env (ci, (p, rci), NoInvert, mkRel 1, [|branch|])), None
  in
  let proj = it_mkLambda_or_LetIn (mkLambda (x,rp,body)) paramdecls in
  let projtyp = it_mkProd_or_LetIn (mkProd (x,rp,ccl)) paramdecls in
  let univs = match fst univs with
  | Entries.Monomorphic_entry ->
    UState.{ universes_entry_universes = UState.Monomorphic_entry Univ.ContextSet.empty;
      universes_entry_binders = snd univs }
  | Entries.Polymorphic_entry (uctx, variances) ->
    let variances = make_projection_variances (Context.Rel.nhyps paramdecls) variances in
    UState.{ universes_entry_universes = UState.Polymorphic_entry (uctx, variances);
      universes_entry_binders = snd univs }
  in
  let entry = Declare.definition_entry ~univs ~types:projtyp proj in
  let kind = Decls.IsDefinition kind in
  let kn =
    (* XXX more precise loc *)
    try Declare.declare_constant ~name:fid ~kind (Declare.DefinitionEntry entry)
    with Type_errors.TypeError (ctx,te) as exn when not primitive ->
      let _, info = Exninfo.capture exn in
      Exninfo.iraise (NotDefinable (BadTypedProj (fid,ctx,te)),info)
  in
  Declare.definition_message fid;
  let term = match p_opt with
    | Some (p,r) ->
      let _ = DeclareInd.declare_primitive_projection p kn in
      mkProj (Projection.make p false, r, mkRel 1)
    | None ->
      let proj_args = (*Rel 1 refers to "x"*) paramargs@[mkRel 1] in
      match decl with
      | LocalDef _ when primitive -> body
      | _ -> applist (mkConstU (kn,uinstance),proj_args)
  in
  let refi = GlobRef.ConstRef kn in
  Impargs.maybe_declare_manual_implicits false refi impls;
  declare_proj_coercion_instance ~flags refi (GlobRef.IndRef indsp);
  let i = if is_local_assum decl then i+1 else i in
  (Some kn, i, Projection term::subst)

(** [build_proj] will build a projection for each field, or skip if
   the field is anonymous, i.e. [_ : t] *)
let build_proj env mib indsp primitive x rp lifted_fields ~poly paramdecls paramargs ~uinstance ~kind ~univs
    (nfi,i,kinds,subst) flags decl impls =
  let fi = RelDecl.get_name decl in
  let ti = RelDecl.get_type decl in
  let (sp_proj,i,subst) =
    match fi with
    | Anonymous ->
      (None,i,NoProjection fi::subst)
    | Name fid ->
      try build_named_proj
            ~primitive ~flags ~poly ~univs ~uinstance ~kind env paramdecls paramargs decl impls fid
            subst nfi ti i indsp mib lifted_fields x rp
      with NotDefinable why as exn ->
        let _, info = Exninfo.capture exn in
        warning_or_error ~info flags indsp why;
        (None,i,NoProjection fi::subst)
  in
  (nfi - 1, i,
   { Structure.proj_name = fi
   ; proj_true = is_local_assum decl
   ; proj_canonical = flags.Data.pf_canonical
   ; proj_body = sp_proj } :: kinds
  , subst)

(** [declare_projections] prepares the common context for all record
   projections and then calls [build_proj] for each one. *)
let declare_projections indsp univs ?(kind=Decls.StructureComponent) inhabitant_id flags fieldimpls fields =
  let env = Global.env() in
  let (mib,mip) = Global.lookup_inductive indsp in
  let poly = Declareops.inductive_is_polymorphic mib in
  let uinstance = match fst univs with
    | Polymorphic_entry (uctx, _) -> UVars.Instance.of_level_instance @@ UVars.UContext.instance uctx
    | Monomorphic_entry -> UVars.Instance.empty
  in
  let paramdecls = Inductive.inductive_paramdecls (mib, uinstance) in
  let r = mkIndU (indsp,uinstance) in
  let rp = applist (r, Context.Rel.instance_list mkRel 0 paramdecls) in
  let paramargs = Context.Rel.instance_list mkRel 1 paramdecls in (*def in [[params;x:rp]]*)
  let x = make_annot (Name inhabitant_id) (Inductive.relevance_of_ind_body mip uinstance) in
  let fields = instantiate_possibly_recursive_type (fst indsp) uinstance mib.mind_ntypes paramdecls fields in
  let lifted_fields = Vars.lift_rel_context 1 fields in
  let primitive =
    match mib.mind_record with
    | PrimRecord _ -> true
    | FakeRecord | NotRecord -> false
  in
  let (_,_,canonical_projections,_) =
    List.fold_left3
      (build_proj env mib indsp primitive x rp lifted_fields ~poly paramdecls paramargs ~uinstance ~kind ~univs)
      (List.length fields,0,[],[]) flags (List.rev fields) (List.rev fieldimpls)
  in
    List.rev canonical_projections

open Typeclasses

let load_structure _ structure = Structure.register structure

let cache_structure o = load_structure 1 o

let subst_structure (subst, obj) = Structure.subst subst obj

let discharge_structure x = Some x

let rebuild_structure s = Structure.rebuild (Global.env()) s

let inStruc : Structure.t -> Libobject.obj =
  let open Libobject in
  declare_object {(default_object "STRUCTURE") with
    cache_function = cache_structure;
    load_function = load_structure;
    subst_function = subst_structure;
    classify_function = (fun _ -> Substitute);
    discharge_function = discharge_structure;
    rebuild_function = rebuild_structure; }

let declare_structure_entry o =
  Lib.add_leaf (inStruc o)

(** In the type of every projection, the record is bound to a variable named
  using the first character of the record type. We rename it to avoid
  collisions with names already used in the field types.
*)

(** Get all names bound at the head of [t]. *)
let rec add_bound_names_constr (names : Id.Set.t) (t : constr) : Id.Set.t =
  match destProd t with
  | (b, _, t) ->
    let names =
      match b.binder_name with
      | Name.Anonymous -> names
      | Name.Name n -> Id.Set.add n names
    in add_bound_names_constr names t
  | exception DestKO -> names

(** Get all names bound in any record field. *)
let bound_names_rdata { DataR.fields; _ } : Id.Set.t =
  let add_names names field = add_bound_names_constr names (RelDecl.get_type field) in
  List.fold_left add_names Id.Set.empty fields

(** Main record declaration part:

   The entry point is [definition_structure], which will match on the
   declared [kind] and then either follow the regular record
   declaration path to [declare_structure] or handle the record as a
   class declaration with [declare_class].

*)

(** [declare_structure] does two principal things:

  - prepares and declares the low-level (mutual) inductive corresponding to [record_data]
  - prepares and declares the corresponding record projections, mainly taken care of by
    [declare_projections]
*)
module Record_decl = struct
  type t = {
    mie : Entries.mutual_inductive_entry;
    default_dep_elim : DeclareInd.default_dep_elim list;
    records : Data.t list;
    primitive_proj : bool;
    impls : DeclareInd.one_inductive_impls list;
    globnames : UState.named_universes_entry;
    global_univ_decls : Univ.ContextSet.t option;
    projunivs : Entries.universes_entry;
    ubinders : UnivNames.universe_binders;
    projections_kind : Decls.definition_object_kind;
    poly : bool;
    indlocs : DeclareInd.indlocs;
  }
end

module Ast = struct
  open Vernacexpr
  type t =
    { name : Names.lident
    ; is_coercion : coercion_flag
    ; binders: local_binder_expr list
    ; cfs : (local_decl_expr * record_field_attr) list
    ; idbuild : lident
    ; sort : constr_expr option
    ; default_inhabitant_id : Id.t option
    }

  let to_datai { name; cfs; sort; _ } =
    let fs = List.map fst cfs in
    { DataI.name = name.CAst.v
    ; arity = sort
    ; nots = List.map (fun (_, { rf_notation }) -> List.map Metasyntax.prepare_where_notation rf_notation) cfs
    ; fs
    }
end

let check_unique_names records =
  let extract_name acc (rf_decl, _) = match rf_decl with
      Vernacexpr.AssumExpr({CAst.v=Name id},_,_) -> id::acc
    | Vernacexpr.DefExpr ({CAst.v=Name id},_,_,_) -> id::acc
    | _ -> acc in
  let indlocs =
    records |> List.map (fun { Ast.name; idbuild; _ } -> name, idbuild ) in
  let fields_names =
    records |> List.fold_left (fun acc { Ast.cfs; _ } ->
      List.fold_left extract_name acc cfs) [] in
  let allnames =
    (* XXX we don't check the name of the constructor ([idbuild])
       because definitional classes ignore it so it being a duplicate must be allowed.

       Maybe we will refactor this someday, or maybe we will remove
       the early check and let declaration fail when there are duplicates. *)
    fields_names @ (indlocs |> List.map (fun (x,_) -> x.CAst.v))
  in
  match List.duplicates Id.equal allnames with
  | [] -> List.map (fun (x,y) -> x.CAst.loc, [y.CAst.loc]) indlocs
  | id :: _ -> user_err (str "Two objects have the same name" ++ spc () ++ quote (Id.print id) ++ str ".")

type kind_class = NotClass | RecordClass | DefClass

let kind_class =
  let open Vernacexpr in
  function Class true -> DefClass | Class false -> RecordClass
  | Inductive_kw | CoInductive | Variant | Record | Structure -> NotClass

(** Pick a variable name for a record, avoiding names bound in its fields. *)
let canonical_inhabitant_id ~isclass ind_id =
  if isclass then ind_id
  else Id.of_string (Unicode.lowercase_first_char (Id.to_string ind_id))

let check_priorities kind records =
  let open Vernacexpr in
  let isnot_class = kind_class kind <> RecordClass in
  let has_priority { Ast.cfs; _ } =
    List.exists (fun (_, { rf_priority }) -> not (Option.is_empty rf_priority)) cfs
  in
  if isnot_class && List.exists has_priority records then
    user_err Pp.(str "Priorities only allowed for type class substructures.")

let extract_record_data records =
  let data = List.map Ast.to_datai records in
  let ps = match records with
  | [] -> CErrors.anomaly (str "Empty record block.")
  | r :: rem ->
    let eq_local_binders bl1 bl2 = List.equal local_binder_eq bl1 bl2 in
    match List.find_opt (fun r' -> not @@ eq_local_binders r.Ast.binders r'.Ast.binders) rem with
    | None -> r.Ast.binders
    | Some r' ->
      ComInductive.Internal.error_differing_params ~kind:"record"
        (r.name, (r.binders,None))
        (r'.name, (r'.binders,None))
  in
  ps, data

let implicits_of_context ctx =
  List.map (fun name -> CAst.make (Some (name,true)))
    (List.rev (Anonymous :: (List.filter_map (function
         | LocalDef _ -> None
         | LocalAssum _ as d -> Some (RelDecl.get_name d))
         ctx)))

let check_proj_flags kind rf =
  let open Vernacexpr in
  let pf_coercion, pf_reversible =
    match rf.rf_coercion with
    | AddCoercion -> true, Option.default true rf.rf_reversible
    | NoCoercion ->
       if rf.rf_reversible <> None then
         Attributes.(unsupported_attributes
           [CAst.make ("reversible (without :>)",VernacFlagEmpty)]);
       false, false in
  let pf_instance =
    match rf.rf_instance with NoInstance -> false | BackInstance -> true in
  let pf_priority = rf.rf_priority in
  let pf_locality =
    begin match rf.rf_coercion, rf.rf_instance with
    | NoCoercion, NoInstance ->
       if rf.rf_locality <> Goptions.OptDefault then
         Attributes.(unsupported_attributes
           [CAst.make ("locality (without :> or ::)",VernacFlagEmpty)])
    | AddCoercion, NoInstance ->
       if rf.rf_locality = Goptions.OptExport then
         Attributes.(unsupported_attributes
           [CAst.make ("export (without ::)",VernacFlagEmpty)])
    | _ -> ()
    end; rf.rf_locality in
  let pf_canonical = rf.rf_canonical in
  Data.{ pf_coercion; pf_reversible; pf_instance; pf_priority; pf_locality; pf_canonical }

let pre_process_structure ~auto_prop_lowering udecl kind ~poly ~cumulative (records : Ast.t list) =
  let indlocs = check_unique_names records in
  let () = check_priorities kind records in
  let ps, data = extract_record_data records in
  let impargs, univs, params, data =
    (* In theory we should be able to use
       [Notation.with_notation_protection], due to the call to
       Metasyntax.set_notation_for_interpretation, however something
       is messing state beyond that.
    *)
    Vernacstate.System.protect (fun () ->
        typecheck_params_and_fields ~auto_prop_lowering (kind = Class true) ~poly ~cumulative udecl ps data) ()
  in
  let adjust_impls impls = match kind_class kind with
    | NotClass -> impargs @ [CAst.make None] @ impls
    | _ -> implicits_of_context params @ impls in
  let data = List.map (fun ({ DataR.implfs; _ } as d) -> { d with DataR.implfs = List.map adjust_impls implfs }) data in
  let map rdata { Ast.name; is_coercion; cfs; idbuild; default_inhabitant_id; _ } =
    let proj_flags = List.map (fun (_, rf) -> check_proj_flags kind rf) cfs in
    let inhabitant_id =
      match default_inhabitant_id with
      | Some n -> n
      | None ->
        let canonical_inhabitant_id = canonical_inhabitant_id ~isclass:(kind_class kind != NotClass) name.CAst.v in
        Namegen.next_ident_away canonical_inhabitant_id (bound_names_rdata rdata)
    in
    let is_coercion = match is_coercion with AddCoercion -> true | NoCoercion -> false in
    { Data.id = name.CAst.v; idbuild = idbuild.v; rdata; is_coercion; proj_flags; inhabitant_id }
  in
  let data = List.map2 map data records in
  let projections_kind =
    Decls.(match kind_class kind with NotClass -> StructureComponent | _ -> Method) in
  impargs, params, univs, projections_kind, data, indlocs

let interp_structure_core ~cumulative finite ~univs ~primitive_proj impargs params template ~projections_kind ~indlocs data =
  let nparams = List.length params in
  let ubinders = univs.UState.universes_entry_binders in
  let poly, projunivs =
    match univs.UState.universes_entry_universes with
    | UState.Monomorphic_entry _ -> false, Entries.Monomorphic_entry
    | UState.Polymorphic_entry (uctx, variances) -> true, Entries.Polymorphic_entry (uctx, variances)
  in
  let ntypes = List.length data in
  let mk_block i { Data.id; idbuild; rdata = { DataR.arity; fields; _ }; _ } =
    let nfields = List.length fields in
    let args = Context.Rel.instance_list mkRel nfields params in
    let ind = applist (mkRel (ntypes - i + nparams + nfields), args) in
    let type_constructor = it_mkProd_or_LetIn ind fields in
    { mind_entry_typename = id;
      mind_entry_arity = arity;
      mind_entry_consnames = [idbuild];
      mind_entry_lc = [type_constructor] }
  in
  let blocks = List.mapi mk_block data in
  let ind_univs, global_univ_decls = match blocks, data with
  | [entry], [data] ->
    ComInductive.compute_template_inductive ~user_template:template
      ~ctx_params:params ~univ_entry:univs.universes_entry_universes entry
      (if Term.isArity entry.mind_entry_arity then SyntaxAllowsTemplatePoly else SyntaxNoTemplatePoly)
  | _ ->
    begin match template with
    | Some true -> user_err Pp.(str "Template-polymorphism not allowed with mutual records.")
    | Some false | None ->
      match univs.universes_entry_universes with
      | UState.Polymorphic_entry (uctx, variances) -> Polymorphic_ind_entry (uctx, variances), Univ.ContextSet.empty
      | UState.Monomorphic_entry uctx -> Monomorphic_ind_entry, uctx
    end
  in
  let globnames, global_univ_decls, univs = match ind_univs with
  | Monomorphic_ind_entry -> univs, Some global_univ_decls, ind_univs
  | Template_ind_entry _ -> univs, Some global_univ_decls, ind_univs
  | Polymorphic_ind_entry (ctx, variances) ->
    let variances = ComInductive.variance_of_entry ~cumulative ctx variances in
    let univs =
      UState.{ universes_entry_universes = Polymorphic_entry (ctx, variances);
               universes_entry_binders = UnivNames.empty_binders }
    in univs, None, Polymorphic_ind_entry (ctx, variances)
  in
  let mie =
    { mind_entry_params = params;
      mind_entry_record = Some (if primitive_proj then Some (Array.map_of_list (fun a -> a.Data.inhabitant_id) data) else None);
      mind_entry_finite = finite;
      mind_entry_inds = blocks;
      mind_entry_private = None;
      mind_entry_universes = univs;
    }
  in
  let impls = List.map (fun _ -> impargs, []) data in
  let default_dep_elim = List.map (fun d -> d.Data.rdata.default_dep_elim) data in
  let open Record_decl in
  { mie; default_dep_elim; primitive_proj; impls; globnames; global_univ_decls; projunivs;
    ubinders; projections_kind; poly; records = data;
    indlocs;
  }


let interp_structure ~flags udecl kind ~primitive_proj records =
  assert (kind <> Vernacexpr.Class true);
  let ComInductive.{
      poly;
      cumulative;
      template;
      auto_prop_lowering;
      finite;
    } = flags in
  let impargs, params, univs, projections_kind, data, indlocs =
    pre_process_structure ~auto_prop_lowering udecl kind ~poly ~cumulative records in
  interp_structure_core ~cumulative finite ~univs ~primitive_proj impargs params template ~projections_kind ~indlocs data

let declare_structure { Record_decl.mie; default_dep_elim; primitive_proj; impls; globnames; global_univ_decls; projunivs; ubinders; projections_kind; poly; records; indlocs } =
  Option.iter Global.push_context_set global_univ_decls;
  let kn = DeclareInd.declare_mutual_inductive_with_eliminations mie globnames impls
      ~primitive_expected:primitive_proj ~indlocs ~default_dep_elim
  in
  let map i { Data.is_coercion; proj_flags; rdata = { DataR.implfs; fields; _}; inhabitant_id; _ } =
    let rsp = (kn, i) in (* This is ind path of idstruc *)
    let cstr = (rsp, 1) in
    let projections = declare_projections rsp (projunivs,ubinders) ~kind:projections_kind inhabitant_id proj_flags implfs fields in
    let build = GlobRef.ConstructRef cstr in
    let () = if is_coercion then ComCoercion.try_add_new_coercion build ~local:false ~reversible:false in
    let struc = Structure.make (Global.env ()) rsp projections in
    let () = declare_structure_entry struc in
    GlobRef.IndRef rsp
  in
  List.mapi map records, []

let get_class_params : Data.t list -> Data.t = function
  | [data] -> data
  | _ ->
    CErrors.user_err (str "Mutual definitional classes are not supported.")

(* declare definitional class (typeclasses that are not record) *)
(* [data] is a list with a single [Data.t] with a single field (in [Data.rdata])
   and [Data.is_coercion] must be [NoCoercion] *)
let declare_class_constant ~univs paramimpls params data =
  let {Data.id; rdata; is_coercion; proj_flags; inhabitant_id} = get_class_params data in
  assert (not is_coercion);  (* should be ensured by caller *)
  let implfs = rdata.DataR.implfs in
  let field, binder, proj_name, proj_flags = match rdata.DataR.fields, proj_flags with
    | [ LocalAssum ({binder_name=Name proj_name} as binder, field)
      | LocalDef ({binder_name=Name proj_name} as binder, _, field) ], [proj_flags] ->
      let binder = {binder with binder_name=Name inhabitant_id} in
      field, binder, proj_name, proj_flags
    | _ -> assert false in  (* should be ensured by caller *)
  let class_body = it_mkLambda_or_LetIn field params in
  let class_type = it_mkProd_or_LetIn rdata.DataR.arity params in
  let class_entry =
    Declare.definition_entry ~types:class_type ~univs class_body in
  let cst = Declare.declare_constant ~name:id
      (Declare.DefinitionEntry class_entry) ~kind:Decls.(IsDefinition Definition)
  in
  let inst, univs = match univs.universes_entry_universes with
    | UState.Monomorphic_entry _ ->
      UVars.Instance.empty,
      UState.{ univs with universes_entry_universes = UState.Monomorphic_entry Univ.ContextSet.empty }
    | UState.Polymorphic_entry (uctx, variances) ->
      UVars.Instance.of_level_instance (UVars.UContext.instance uctx), univs
  in
  let cstu = (cst, inst) in
  let inst_type = appvectc (mkConstU cstu) (Context.Rel.instance mkRel 0 params) in
  let proj_type =
    it_mkProd_or_LetIn (mkProd(binder, inst_type, lift 1 field)) params in
  let proj_body =
    it_mkLambda_or_LetIn (mkLambda (binder, inst_type, mkRel 1)) params in
  let proj_entry = Declare.definition_entry ~types:proj_type ~univs proj_body in
  let proj_cst = Declare.declare_constant ~name:proj_name
      (Declare.DefinitionEntry proj_entry) ~kind:Decls.(IsDefinition Definition)
  in
  let cref = GlobRef.ConstRef cst in
  Impargs.declare_manual_implicits false cref paramimpls;
  Impargs.declare_manual_implicits false (GlobRef.ConstRef proj_cst) (List.hd implfs);
  Classes.set_typeclass_transparency ~locality:Hints.SuperGlobal
    [Evaluable.EvalConstRef cst] false;
  let () =
    declare_proj_coercion_instance ~flags:proj_flags (GlobRef.ConstRef proj_cst) cref in
  let m = {
    meth_name = Name proj_name;
    meth_info = None;
    meth_const = Some proj_cst;
  } in
  [cref], [m]


let set_class_mode ref mode ctx =
  let modes =
    match mode with
    | Some (Some m) -> Some m
    | _ ->
      let ctxl = Context.Rel.nhyps ctx in
      let def = typeclasses_default_mode () in
      let mode = match def with
      | Hints.ModeOutput -> None
      | Hints.ModeInput ->
        Some (List.init ctxl (fun _ -> Hints.ModeInput))
      | Hints.ModeNoHeadEvar ->
        Some (List.init ctxl (fun _ -> Hints.ModeNoHeadEvar))
      in
      let wm = List.init ctxl (fun _ -> def) in
      Classes.warn_default_mode (ref, wm);
      mode
  in
  match modes with
  | None -> ()
  | Some modes -> Classes.set_typeclass_mode ~locality:Hints.SuperGlobal ref modes


(** [declare_class] will prepare and declare a [Class]. This is done in
   2 steps:

  1. two markedly different paths are followed depending on whether the
   class declaration refers to a constant "definitional classes"
   (with [declare_class_constant]) or to a record (with [declare_structure]),
   that is to say:

      Class foo := bar : T.

    which is equivalent to

      Definition foo := T.
      Definition bar (x:foo) : T := x.
      Existing Class foo.

    vs

      Class foo := { ... }.

  2. now, declare the class, using the information ([inds] and [def]) from 1.
   in the form of [Classes.typeclass]

  *)
let declare_class ~univs params inds def ?mode data =
  let { Data.rdata } = get_class_params data in
  let fields = rdata.DataR.fields in
  let map ind =
    let map decl y = {
      meth_name = RelDecl.get_name decl;
      meth_info = None;
      meth_const = y;
    } in
    let l = match ind with
      | GlobRef.IndRef ind ->
         List.map2 map (List.rev fields) (Structure.find_projections ind)
      | _ -> def in
    ind, l
  in
  let data = List.map map inds in
  let univs, params, fields =
    match univs.UState.universes_entry_universes with
    | UState.Polymorphic_entry (uctx, variances) ->
      let usubst, auctx = UVars.abstract_universes uctx in
      let usubst = UVars.make_instance_subst usubst in
      let map c = Vars.subst_univs_level_constr usubst c in
      let fields = Context.Rel.map map fields in
      let params = Context.Rel.map map params in
      auctx, params, fields
    | UState.Monomorphic_entry _ ->
      UVars.AbstractContext.empty, params, fields
  in
  let map (impl, projs) =
    let k =
      { cl_univs = univs;
        cl_impl = impl;
        cl_strict = typeclasses_strict ();
        cl_unique = typeclasses_unique ();
        cl_context = params;
        cl_props = fields;
        cl_projs = projs }
    in
    Classes.add_class k;
    set_class_mode impl mode params
  in
  List.iter map data

let add_constant_class cst =
  let env = Global.env () in
  let ty, univs = Typeops.type_of_global_in_context env (GlobRef.ConstRef cst) in
  let r = (Environ.lookup_constant cst env).const_relevance in
  let ctx, _ = decompose_prod_decls ty in
  let args = Context.Rel.instance Constr.mkRel 0 ctx in
  let t = mkApp (mkConstU (cst, UVars.make_abstract_instance univs), args) in
  let tc =
    { cl_univs = univs;
      cl_impl = GlobRef.ConstRef cst;
      cl_context = ctx;
      cl_props = [LocalAssum (make_annot Anonymous r, t)];
      cl_projs = [];
      cl_strict = typeclasses_strict ();
      cl_unique = typeclasses_unique ()
    }
  in
  Classes.add_class tc;
  Classes.set_typeclass_transparency ~locality:Hints.SuperGlobal
    [Evaluable.EvalConstRef cst] false

let add_inductive_class ind =
  let env = Global.env () in
  let mind, oneind = Inductive.lookup_mind_specif env ind in
  let ctx = oneind.mind_arity_ctxt in
  let k =
    let univs = Declareops.inductive_polymorphic_context mind in
    let inst = UVars.make_abstract_instance univs in
    let ty = Inductive.type_of_inductive ((mind, oneind), inst) in
    let r = oneind.mind_relevance in
      { cl_univs = univs;
        cl_impl = GlobRef.IndRef ind;
        cl_context = ctx;
        cl_props = [LocalAssum (make_annot Anonymous r, ty)];
        cl_projs = [];
        cl_strict = typeclasses_strict ();
        cl_unique = typeclasses_unique () }
  in
  Classes.add_class k

let warn_already_existing_class =
  CWarnings.create ~name:"already-existing-class" ~category:CWarnings.CoreCategories.automation Pp.(fun g ->
      Printer.pr_global g ++ str " is already declared as a typeclass.")

let declare_existing_class g =
  if Typeclasses.is_class g then warn_already_existing_class g
  else
    match g with
    | GlobRef.ConstRef x -> add_constant_class x
    | GlobRef.IndRef x -> add_inductive_class x
    | _ -> user_err
             (Pp.str"Unsupported class type, only constants and inductives are allowed.")

(** [fs] corresponds to fields and [ps] to parameters; [proj_flags] is a
    list telling if the corresponding fields must me declared as coercions
    or subinstances. *)

let definition_structure ~flags udecl kind ~primitive_proj (records : Ast.t list)
  : GlobRef.t list =
  let ComInductive.{
      poly;
      cumulative;
      template;
      auto_prop_lowering;
      finite;
    } = flags in
  let impargs, params, univs, projections_kind, data, indlocs =
    pre_process_structure ~auto_prop_lowering udecl kind ~poly ~cumulative records
  in
  let inds, def = match kind_class kind with
    | DefClass -> declare_class_constant ~univs impargs params data
    | RecordClass | NotClass ->
      let structure =
        interp_structure_core
          ~cumulative finite ~univs ~primitive_proj
          impargs params template ~projections_kind ~indlocs data in
      declare_structure structure
  in
  if kind_class kind <> NotClass then declare_class ~univs params inds def ~mode:flags.mode data;
  inds

module Internal = struct
  type nonrec projection_flags = Data.projection_flags = {
    pf_coercion: bool;
    pf_reversible: bool;
    pf_instance: bool;
    pf_priority: int option;
    pf_locality: Goptions.option_locality;
    pf_canonical: bool;
  }
  let declare_projections = declare_projections
  let declare_structure_entry = declare_structure_entry
end
