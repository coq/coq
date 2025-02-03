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
  | { CAst.v = CSort s } -> Constrexpr_ops.(sort_expr_eq expr_Type_sort s)
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
    ; constructor_name : Id.t
    ; arity : Constrexpr.constr_expr option
    (** declared sort for the record  *)
    ; nots : Metasyntax.notation_interpretation_decl list list
    (** notations for fields *)
    ; fs : Vernacexpr.local_decl_expr list
    ; default_inhabitant_id : Id.t option
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
  type t =
  { is_coercion : Vernacexpr.coercion_flag
  ; proj_flags : projection_flags list
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
    let sigma, s = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
    sigma, (EConstr.mkSort s, s)
  | Some { CAst.v = CSort s; loc } when Constrexpr_ops.(sort_expr_eq expr_Type_sort s) ->
    (* special case: the user wrote ": Type". We want to allow it to become algebraic
       (and Prop but that may change in the future) *)
    let sigma, s = Evd.new_sort_variable ?loc UState.univ_flexible_alg sigma in
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

module DefClassEntry = struct

type t = {
  univs : UState.named_universes_entry;
  name : Id.t;
  projname : Id.t;
  params : Constr.rel_context;
  sort : Sorts.t;
  typ : Constr.t; (* NB: typ is convertible to sort *)
  projtyp : Constr.t;
  inhabitant_id : Id.t;
  impls : Impargs.manual_implicits;
  projimpls : Impargs.manual_implicits;
}

end

module RecordEntry = struct

  type one_ind_info = {
    (* inhabitant_id not redundant with the entry in non prim record case *)
    inhabitant_id : Id.t;
    default_dep_elim : DeclareInd.default_dep_elim;
    (* implfs includes the param and principal argument info *)
    implfs : Impargs.manual_implicits list;
  }

  let make_ind_infos id elims implfs =
    { inhabitant_id = id;
      default_dep_elim = elims;
      implfs;
    }

  type t = {
    global_univs : Univ.ContextSet.t;
    ubinders : UState.named_universes_entry;
    mie : Entries.mutual_inductive_entry;
    ind_infos : one_ind_info list;
    param_impls : Impargs.manual_implicits;
  }

end

type defclass_or_record =
  | DefclassEntry of DefClassEntry.t
  | RecordEntry of RecordEntry.t

(* we currently don't check that defclasses are nonrecursive until we try to declare the definition in the kernel
   so we do need env_ar_params (instead of env_params) to avoid unbound rel anomalies *)
let def_class_levels ~def ~env_ar_params sigma aritysorts ctors =
  let s, projname, ctor = match aritysorts, ctors with
    | [s], [ctor] -> begin match ctor with
        | [LocalAssum (na,t)] -> s, na.binder_name, t
        | _ -> assert false
      end
    | _ -> CErrors.user_err Pp.(str "Mutual definitional classes are not supported.")
  in
  let projname = match projname with
    | Name id -> id
    | Anonymous -> assert false
  in
  let ctor_sort = Retyping.get_sort_of env_ar_params sigma ctor in
  let is_prop_ctor = EConstr.ESorts.is_prop sigma ctor_sort in
  let sigma = Evd.set_leq_sort sigma ctor_sort s in
  if Option.cata (Evd.is_flexible_level sigma) false (is_sort_variable sigma s)
  && is_prop_ctor
  then (* We assume that the level in aritysort is not constrained
          and clear it, if it is flexible *)
    let sigma = Evd.set_eq_sort sigma EConstr.ESorts.set s in
    sigma, EConstr.ESorts.prop, projname, ctor
  else
    sigma, s, projname, ctor

let finalize_def_class env sigma ~params ~sort ~projtyp =
  let sigma, (params, sort, typ, projtyp) =
    Evarutil.finalize ~abort_on_undefined_evars:false sigma (fun nf ->
        let typ = EConstr.it_mkProd_or_LetIn (EConstr.mkSort sort) params in
        let typ = nf typ in
        (* we know the context is exactly the params because we built typ from mkSort *)
        let params, typ = Term.decompose_prod_decls typ in
        let projtyp = nf projtyp in
        let sort = destSort (nf (EConstr.mkSort sort)) in
        params, sort, typ, projtyp)
  in
  let ce t = Pretyping.check_evars env sigma (EConstr.of_constr t) in
  (* no need to check evars in typ which is guaranteed to be a sort  *)
  let () = Context.Rel.iter ce params in
  let () = ce projtyp in
  sigma, params, sort, typ, projtyp

let adjust_field_implicits ~isclass (params,param_impls) (impls:Impargs.manual_implicits) =
  let main_arg = if isclass then Some (Anonymous, true) else None in
  let param_impls = if isclass then
      List.rev (List.filter_map (fun d ->
          if RelDecl.is_local_def d then None
          else Some (CAst.make (Some (RelDecl.get_name d, true))))
          params)
    else param_impls
  in
  param_impls @ (CAst.make main_arg :: impls)

type kind_class = NotClass | RecordClass | DefClass

(** Pick a variable name for a record, avoiding names bound in its fields. *)
let canonical_inhabitant_id ~isclass ind_id =
  if isclass then ind_id
  else Id.of_string (Unicode.lowercase_first_char (Id.to_string ind_id))

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
let bound_names_ind_entry (ind:Entries.one_inductive_entry) : Id.Set.t =
  let ctor = match ind.mind_entry_lc with
    | [ctor] -> ctor
    | _ -> assert false
  in
  let fields, _ = Term.decompose_prod_decls ctor in
  let add_names names field = add_bound_names_constr names (RelDecl.get_type field) in
  List.fold_left add_names Id.Set.empty fields

let inhabitant_id ~isclass bound_names ind {DataI.default_inhabitant_id=id; name} =
  match id with
  | Some id -> id
  | None ->
    let canonical_inhabitant_id = canonical_inhabitant_id ~isclass name in
    (* In the type of every projection, the record is bound to a
        variable named using the first character of the record type.
        We rename it to avoid collisions with names already used in
        the field types. *)
    Namegen.next_ident_away canonical_inhabitant_id (bound_names ind)

let fix_entry_record ~isclass ~primitive_proj records mie =
  let ids = List.map2 (inhabitant_id ~isclass bound_names_ind_entry) mie.mind_entry_inds records in
  if not primitive_proj then
    ids, { mie with mind_entry_record = Some None }
  else
    ids, { mie with mind_entry_record = Some (Some (Array.of_list ids)) }

let typecheck_params_and_fields ~kind ~(flags:ComInductive.flags) ~primitive_proj udecl params (records : DataI.t list) =
  let def = kind = DefClass in
  let isclass = kind != NotClass in
  let env0 = Global.env () in
  (* Special case elaboration for template-polymorphic inductives,
     lower bound on introduced universes is Prop so that we do not miss
     any Set <= i constraint for universes that might actually be instantiated with Prop. *)
  let is_template =
    List.exists (fun { DataI.arity; _} -> Option.cata check_anonymous_type true arity) records in
  let unconstrained_sorts = not flags.poly && not def && is_template in
  let sigma, udecl, variances = Constrintern.interp_cumul_univ_decl_opt env0 udecl in
  let () = List.iter check_parameters_must_be_named params in
  let sigma, (impls_env, ((_env1,params), impls)) =
    Constrintern.interp_context_evars ~program_mode:false ~unconstrained_sorts env0 sigma params in
  let sigma, typs =
    List.fold_left_map (build_type_telescope ~unconstrained_sorts params env0) sigma records in
  let typs, aritysorts = List.split typs in
  let arities = List.map (fun typ -> EConstr.it_mkProd_or_LetIn typ params) typs in
  let relevances = List.map (fun s -> EConstr.ESorts.relevance_of_sort s) aritysorts in
  let fold accu { DataI.name; _ } arity r =
    EConstr.push_rel (LocalAssum (make_annot (Name name) r,arity)) accu in
  let env_ar_params = EConstr.push_rel_context params (List.fold_left3 fold env0 records arities relevances) in
  let impls_env =
    let ids = List.map (fun { DataI.name; _ } -> name) records in
    let impls = List.map (fun _ -> impls) arities in
    Constrintern.compute_internalization_env env0 sigma ~impls:impls_env Constrintern.Inductive ids arities impls
  in
  let ninds = List.length arities in
  let nparams = List.length params in
  let fold sigma { DataI.nots; fs; _ } =
    interp_fields_evars env_ar_params sigma ~ninds ~nparams impls_env nots fs
  in
  let (sigma, fields) = List.fold_left_map fold sigma records in
  let field_impls, fields = List.split fields in
  let field_impls = List.map (List.map (adjust_field_implicits ~isclass (params,impls))) field_impls in
  let sigma =
    Pretyping.solve_remaining_evars Pretyping.all_and_fail_flags env_ar_params sigma in
  if def then
    (* XXX to fix: if we enter [Class Foo : typ := Bar : nat.], [typ] will get unfolded here *)
    let sigma, sort, projname, projtyp = def_class_levels ~def ~env_ar_params sigma aritysorts fields in
    let sigma, params, sort, typ, projtyp =
      (* named and rel context in the env don't matter here
         (they will be replaced by the ones of the unsolved evars in the error message
         which is the env's only use) *)
      finalize_def_class env_ar_params sigma ~params ~sort ~projtyp
    in
    let name = match records with
      | [data] -> data.name
      | _ -> assert false
    in
    let univs = Evd.check_univ_decl ~poly:flags.poly sigma udecl in
    (* definitional classes are encoded as 1 constructor with 1
       field whose type is the projection type *)
    let projimpls = match field_impls with
      | [[x]] -> x
      | _ -> assert false
    in
    let inhabitant_id =
      inhabitant_id ~isclass (add_bound_names_constr Id.Set.empty) projtyp (List.hd records)
    in
    DefclassEntry {
      univs;
      name;
      projname;
      params;
      sort;
      typ;
      projtyp;
      inhabitant_id;
      impls;
      projimpls;
    }
  else
    (* each inductive has one constructor *)
    let ninds = List.length arities in
    let nparams = List.length params in
    let constructors = List.map2_i (fun i record fields ->
        let open EConstr in
        let nfields = List.length fields in
        let ind_args = Context.Rel.instance_list mkRel nfields params in
        let ind = applist (mkRel (ninds - i + nparams + nfields), ind_args) in
        let ctor = it_mkProd_or_LetIn ind fields in
        [record.DataI.constructor_name], [ctor])
        0 records fields
    in
    let indnames = List.map (fun x -> x.DataI.name) records in
    let arities_explicit = List.map (fun x -> Option.has_some x.DataI.arity) records in
    let template_syntax = List.map (fun typ ->
        if EConstr.isArity sigma typ then
          ComInductive.SyntaxAllowsTemplatePoly
        else ComInductive.SyntaxNoTemplatePoly)
        typs
    in
    let env_ar = Environ.pop_rel_context nparams env_ar_params in
    let default_dep_elim, mie, ubinders, global_univs =
      ComInductive.interp_mutual_inductive_constr ~sigma ~flags ~udecl ~variances
        ~ctx_params:params ~indnames ~arities_explicit ~arities:typs ~constructors
        ~template_syntax ~env_ar ~private_ind:false
    in
    let ids, mie = fix_entry_record ~isclass ~primitive_proj records mie in
    RecordEntry {
      mie;
      global_univs;
      ubinders;
      ind_infos = List.map3 RecordEntry.make_ind_infos ids default_dep_elim field_impls;
      param_impls = impls;
    }

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

(* TODO: refactor the declaration part here; this requires some
   surgery as Evarutil.finalize is called too early in the path *)
(** This builds and _declares_ a named projection, the code looks
   tricky due to the term manipulation. It also handles declaring the
   implicits parameters, coercion status, etc... of the projection;
   this could be refactored as noted above by moving to the
   higher-level declare constant API *)
let build_named_proj ~primitive ~flags ~univs ~uinstance ~kind env paramdecls
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
let build_proj env mib indsp primitive x rp lifted_fields paramdecls paramargs ~uinstance ~kind ~univs
    (nfi,i,kinds,subst) flags decl impls =
  let fi = RelDecl.get_name decl in
  let ti = RelDecl.get_type decl in
  let (sp_proj,i,subst) =
    match fi with
    | Anonymous ->
      (None,i,NoProjection fi::subst)
    | Name fid ->
      try build_named_proj
            ~primitive ~flags ~univs ~uinstance ~kind env paramdecls paramargs decl impls fid
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
let declare_projections indsp ~kind ~inhabitant_id flags fieldimpls =
  let env = Global.env() in
  let (mib,mip) = Global.lookup_inductive indsp in
  let uinstance =
    UVars.Instance.abstract_instance @@
    UVars.AbstractContext.size @@
    Declareops.inductive_polymorphic_context mib
  in
  let univs = match mib.mind_universes with
    | Monomorphic -> UState.Monomorphic_entry Univ.ContextSet.empty
    | Polymorphic auctx -> UState.Polymorphic_entry (UVars.AbstractContext.repr auctx)
  in
  let univs = univs, UnivNames.empty_binders in
  let fields, _ = mip.mind_nf_lc.(0) in
  let fields = List.firstn mip.mind_consnrealdecls.(0) fields in
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
      (build_proj env mib indsp primitive x rp lifted_fields paramdecls paramargs ~uinstance ~kind ~univs)
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
    entry : RecordEntry.t;
    records : Data.t list;
    projections_kind : Decls.definition_object_kind;
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

  let to_datai { name; idbuild; cfs; sort; default_inhabitant_id; } =
    let fs = List.map fst cfs in
    { DataI.name = name.CAst.v
    ; constructor_name = idbuild.CAst.v
    ; arity = sort
    ; nots = List.map (fun (_, { rf_notation }) -> List.map Metasyntax.prepare_where_notation rf_notation) cfs
    ; fs
    ; default_inhabitant_id
    }
end

let check_unique_names ~def records =
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
    (* we don't check the name of the constructor when [def] because
       definitional class are encoded as 1 constructor of 1 field
       sharing the same name. *)
    let indnames = indlocs |> List.concat_map (fun (x,y) ->
        x.CAst.v :: if def then [] else [y.CAst.v])
    in
    fields_names @ indnames
  in
  match List.duplicates Id.equal allnames with
  | [] -> List.map (fun (x,y) -> x.CAst.loc, [y.CAst.loc]) indlocs
  | id :: _ -> user_err (str "Two objects have the same name" ++ spc () ++ quote (Id.print id) ++ str ".")

let kind_class =
  let open Vernacexpr in
  function Class true -> DefClass | Class false -> RecordClass
  | Inductive_kw | CoInductive | Variant | Record | Structure -> NotClass

let check_priorities kind records =
  let open Vernacexpr in
  let isnot_class = kind_class kind <> RecordClass in
  let has_priority { Ast.cfs; _ } =
    List.exists (fun (_, { rf_priority }) -> not (Option.is_empty rf_priority)) cfs
  in
  if isnot_class && List.exists has_priority records then
    user_err Pp.(str "Priorities only allowed for type class substructures.")

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

let extract_record_data kind records =
  let data = List.map Ast.to_datai records in
  let decl_data = List.map (fun { Ast.is_coercion; cfs } ->
      let proj_flags = List.map (fun (_,rf) -> check_proj_flags kind rf) cfs in
      { Data.is_coercion; proj_flags })
      records
  in
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
  ps, data, decl_data

let pre_process_structure udecl kind ~flags ~primitive_proj (records : Ast.t list) =
  let def = (kind = Vernacexpr.Class true) in
  let indlocs = check_unique_names ~def records in
  let () = check_priorities kind records in
  let ps, interp_data, decl_data = extract_record_data kind records in
  let entry =
    (* In theory we should be able to use
       [Notation.with_notation_protection], due to the call to
       Metasyntax.set_notation_for_interpretation, however something
       is messing state beyond that.
    *)
    Vernacstate.System.protect (fun () ->
        typecheck_params_and_fields ~primitive_proj ~kind:(kind_class kind) ~flags udecl ps interp_data) ()
  in
  let projections_kind =
    Decls.(match kind_class kind with NotClass -> StructureComponent | _ -> Method) in
  entry, projections_kind, decl_data, indlocs

let interp_structure_core (entry:RecordEntry.t) ~projections_kind ~indlocs data =
  let open Record_decl in
  { entry;
    projections_kind;
    records = data;
    indlocs;
  }

let interp_structure ~flags udecl kind ~primitive_proj records =
  assert (kind <> Vernacexpr.Class true);
  let entry, projections_kind, data, indlocs =
    pre_process_structure udecl kind ~flags ~primitive_proj records in
  match entry with
  | DefclassEntry _ -> assert false
  | RecordEntry entry ->
    interp_structure_core entry ~projections_kind ~indlocs data

module Declared = struct
  type t =
    | Defclass of { class_kn : Constant.t; proj_kn : Constant.t; }
    | Record of MutInd.t
end

let declare_structure (decl:Record_decl.t) =
  Global.push_context_set decl.entry.global_univs;
  (* XXX no implicit arguments for constructors? *)
  let impls = List.make (List.length decl.entry.mie.mind_entry_inds) (decl.entry.param_impls, []) in
  let default_dep_elim = List.map (fun x -> x.RecordEntry.default_dep_elim) decl.entry.ind_infos in
  let kn =
    DeclareInd.declare_mutual_inductive_with_eliminations decl.entry.mie
      decl.entry.ubinders
      impls
      ~indlocs:decl.indlocs
      ~default_dep_elim
  in
  let map i ({ RecordEntry.inhabitant_id; implfs }, { Data.is_coercion; proj_flags; }) =
    let rsp = (kn, i) in (* This is ind path of idstruc *)
    let cstr = (rsp, 1) in
    let kind = decl.projections_kind in
    let projections = declare_projections rsp ~kind ~inhabitant_id proj_flags implfs in
    let build = GlobRef.ConstructRef cstr in
    let () = match is_coercion with
      | NoCoercion -> ()
      | AddCoercion -> ComCoercion.try_add_new_coercion build ~local:false ~reversible:false
    in
    let struc = Structure.make (Global.env ()) rsp projections in
    let () = declare_structure_entry struc in
    GlobRef.IndRef rsp
  in
  let data = List.combine decl.entry.ind_infos decl.records in
  let inds = List.mapi map data in
  Declared.Record kn, inds

(* declare definitional class (typeclasses that are not record) *)
(* [data.is_coercion] must be [NoCoercion] and [data.proj_flags] must have exactly 1 element. *)
let declare_class_constant entry (data:Data.t) =
  let { DefClassEntry.univs; name; projname; params; sort; typ; projtyp;
        inhabitant_id; impls; projimpls; }
    = entry
  in
  let {Data.is_coercion; proj_flags} = data in
  let proj_flags = match proj_flags with
    | [x] -> x
    | _ -> assert false
  in
  let () =
    (* should be ensured by caller *)
    match is_coercion with
    | NoCoercion -> ()
    | AddCoercion -> assert false
  in
  let class_body = it_mkLambda_or_LetIn projtyp params in
  let class_type = it_mkProd_or_LetIn typ params in
  let class_entry =
    Declare.definition_entry ~types:class_type ~univs class_body in
  let cst = Declare.declare_constant ~name
      (Declare.DefinitionEntry class_entry) ~kind:Decls.(IsDefinition Definition)
  in
  let inst, univs = match univs with
    | UState.Monomorphic_entry _, ubinders ->
      UVars.Instance.empty, (UState.Monomorphic_entry Univ.ContextSet.empty, ubinders)
    | UState.Polymorphic_entry uctx, _ ->
      UVars.UContext.instance uctx, univs
  in
  let cstu = (cst, inst) in
  let binder =
    let r = Sorts.relevance_of_sort sort in
    { Context.binder_name = Name inhabitant_id; binder_relevance = r }
  in
  let inst_type = appvectc (mkConstU cstu) (Context.Rel.instance mkRel 0 params) in
  let proj_type =
    it_mkProd_or_LetIn (mkProd(binder, inst_type, lift 1 projtyp)) params in
  let proj_body =
    it_mkLambda_or_LetIn (mkLambda (binder, inst_type, mkRel 1)) params in
  let proj_entry = Declare.definition_entry ~types:proj_type ~univs proj_body in
  let proj_cst = Declare.declare_constant ~name:projname
      (Declare.DefinitionEntry proj_entry) ~kind:Decls.(IsDefinition Definition)
  in
  let cref = GlobRef.ConstRef cst in
  Impargs.declare_manual_implicits false cref impls;
  Impargs.declare_manual_implicits false (GlobRef.ConstRef proj_cst) projimpls;
  Classes.set_typeclass_transparency ~locality:Hints.SuperGlobal
    [Evaluable.EvalConstRef cst] false;
  let () =
    declare_proj_coercion_instance ~flags:proj_flags (GlobRef.ConstRef proj_cst) cref in
  Declared.Defclass { class_kn = cst; proj_kn = proj_cst }, [cref]

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


(** [declare_class] declares the typeclass information for a [Class] declaration.
    NB: [Class] syntax does not allow [with]. *)
let declare_class ?mode declared =
  let env = Global.env() in
  let impl, univs, params, fields, projs = match declared with
    | Declared.Defclass { class_kn; proj_kn } ->
      let class_cb = Environ.lookup_constant class_kn env in
      let proj_cb = Environ.lookup_constant proj_kn env in
      let univs = Declareops.constant_polymorphic_context class_cb in
      let class_body = match class_cb.const_body with
        | Def c -> c
        | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> assert false
      in
      let params, field = Term.decompose_lambda_decls class_body in
      let fname = Name (Label.to_id @@ Constant.label proj_kn) in
      let frelevance = proj_cb.const_relevance in
      let fields = [ RelDecl.LocalAssum ({binder_name=fname; binder_relevance=frelevance}, field) ] in
      let proj = {
        Typeclasses.meth_name = fname;
        meth_const = Some proj_kn;
      }
      in
      GlobRef.ConstRef class_kn, univs, params, fields, [proj]
    | Declared.Record mind ->
      let mib, mip = Inductive.lookup_mind_specif env (mind,0) in
      let univs = Declareops.inductive_polymorphic_context mib in
      let ctor_args, _ = mip.mind_nf_lc.(0) in
      let fields = List.firstn mip.mind_consnrealdecls.(0) ctor_args in
      let make_proj decl kn = {
        Typeclasses.meth_name = RelDecl.get_name decl;
        meth_const = kn;
      }
      in
      let projs = List.map2 make_proj (List.rev fields) (Structure.find_projections (mind,0)) in
      GlobRef.IndRef (mind, 0), univs, mib.mind_params_ctxt, fields, projs
  in
  let k = {
    cl_univs = univs;
    cl_impl = impl;
    cl_strict = typeclasses_strict ();
    cl_unique = typeclasses_unique ();
    cl_context = params;
    cl_trivial = CList.is_empty fields;
    cl_props = fields;
    cl_projs = projs;
  }
  in
  Classes.add_class k;
  set_class_mode impl mode params

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
      cl_trivial = false;
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
  let univs = Declareops.inductive_polymorphic_context mind in
  let props, projs =
    match Structure.find ind with
    | exception Not_found ->
      let r = oneind.mind_relevance in
      let args = Context.Rel.instance mkRel 0 ctx in
      let ty = mkApp (mkIndU (ind, UVars.make_abstract_instance univs), args) in
      [LocalAssum (make_annot Anonymous r, ty)], []
    | s ->
      let props, _ = oneind.mind_nf_lc.(0) in
      let props = List.firstn oneind.mind_consnrealdecls.(0) props in
      let projs = s.projections |> List.map (fun (p:Structure.projection) ->
          { meth_name = p.proj_name; meth_const = p.proj_body })
      in
      props, projs
  in
  let k = {
    cl_univs = univs;
    cl_impl = GlobRef.IndRef ind;
    cl_context = ctx;
    cl_trivial = false;
    cl_props = props;
    cl_projs = projs;
    cl_strict = typeclasses_strict ();
    cl_unique = typeclasses_unique ();
  }
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
  let entry, projections_kind, data, indlocs =
    pre_process_structure udecl kind ~flags ~primitive_proj records
  in
  let declared, inds = match entry with
    | DefclassEntry entry ->
      let data = match data with [x] -> x | _ -> assert false in
      declare_class_constant entry data
    | RecordEntry entry ->
      let structure = interp_structure_core entry ~projections_kind ~indlocs data in
      declare_structure structure
  in
  if kind_class kind <> NotClass then declare_class ~mode:flags.mode declared;
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
