(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
module CVars = Vars
open Names
open EConstr
open CErrors
open Util
open Typeclasses_errors
open Typeclasses
open Libnames
open Globnames
open Constrintern
open Constrexpr
open Context.Rel.Declaration
open Class_tactics
open Libobject

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration
(*i*)

let set_typeclass_transparency c local b =
  let locality = if local then Goptions.OptLocal else Goptions.OptGlobal in
  Hints.add_hints ~locality [typeclasses_db]
    (Hints.HintsTransparencyEntry (Hints.HintsReferences [c], b))

let classes_transparent_state () =
  try
    Hints.Hint_db.transparent_state (Hints.searchtable_map typeclasses_db)
  with Not_found -> TransparentState.empty

let () =
  Hook.set Typeclasses.classes_transparent_state_hook classes_transparent_state

let add_instance_hint inst path ~locality info poly =
     Flags.silently (fun () ->
       Hints.add_hints ~locality [typeclasses_db]
          (Hints.HintsResolveEntry
             [info, poly, false, Hints.PathHints path, inst])) ()

let is_local_for_hint i =
  match i.is_global with
  | None -> true  (* i.e. either no Global keyword not in section, or in section *)
  | Some n -> n <> 0 (* i.e. in a section, declare the hint as local
                        since discharge is managed by rebuild_instance which calls again
                        add_instance_hint; don't ask hints to take discharge into account
                        itself *)

let add_instance_base inst =
  let poly = Global.is_polymorphic inst.is_impl in
  let locality = if is_local_for_hint inst then Goptions.OptLocal else Goptions.OptGlobal in
  add_instance_hint (Hints.IsGlobRef inst.is_impl) [inst.is_impl] ~locality
    inst.is_info poly;
  List.iter (fun (path, pri, c) ->
    let h = Hints.IsConstr (EConstr.of_constr c, Univ.ContextSet.empty) [@ocaml.warning "-3"] in
    add_instance_hint h path
                ~locality pri poly)
    (build_subclasses ~check:(not (isVarRef inst.is_impl))
       (Global.env ()) (Evd.from_env (Global.env ())) inst.is_impl inst.is_info)

let mk_instance cl info glob impl =
  let global =
    if glob then Some (Lib.sections_depth ())
    else None
  in
  if match global with Some n -> n>0 && isVarRef impl | _ -> false then
    CErrors.user_err (Pp.str "Cannot set Global an instance referring to a section variable.");
  { is_class = cl.cl_impl;
    is_info = info ;
    is_global = global ;
    is_impl = impl }

(*
 * instances persistent object
 *)
let cache_instance (_, i) =
  load_instance i

let subst_instance (subst, inst) =
  { inst with
      is_class = fst (subst_global subst inst.is_class);
      is_impl = fst (subst_global subst inst.is_impl) }

let discharge_instance (_, inst) =
  match inst.is_global with
  | None -> None
  | Some n ->
    assert (not (isVarRef inst.is_impl));
    Some
    { inst with
      is_global = Some (pred n);
      is_class = inst.is_class;
      is_impl = inst.is_impl }

let is_local i = (i.is_global == None)

let rebuild_instance inst =
  add_instance_base inst;
  inst

let classify_instance inst =
  if is_local inst then Dispose
  else Substitute inst

let instance_input : instance -> obj =
  declare_object
    { (default_object "type classes instances state") with
      cache_function = cache_instance;
      load_function = (fun _ x -> cache_instance x);
      open_function = (fun _ x -> cache_instance x);
      classify_function = classify_instance;
      discharge_function = discharge_instance;
      rebuild_function = rebuild_instance;
      subst_function = subst_instance }

let add_instance i =
  Lib.add_anonymous_leaf (instance_input i);
  add_instance_base i

let warning_not_a_class =
  let name = "not-a-class" in
  let category = "typeclasses" in
  CWarnings.create ~name ~category (fun (n, ty) ->
      let env = Global.env () in
      let evd = Evd.from_env env in
      Pp.(str "Ignored instance declaration for “"
          ++ Nametab.pr_global_env Id.Set.empty n
          ++ str "”: “"
          ++ Termops.Internal.print_constr_env env evd (EConstr.of_constr ty)
          ++ str "” is not a class")
    )

let declare_instance ?(warn = false) env sigma info local glob =
  let ty, _ = Typeops.type_of_global_in_context env glob in
  let info = Option.default {hint_priority = None; hint_pattern = None} info in
  match class_of_constr env sigma (EConstr.of_constr ty) with
  | Some (rels, ((tc,_), args) as _cl) ->
    assert (not (isVarRef glob) || local);
    add_instance (mk_instance tc info (not local) glob)
  | None -> if warn then warning_not_a_class (glob, ty)

(*
 * classes persistent object
 *)

let cache_class (_,c) = load_class c

let subst_class (subst,cl) =
  let do_subst_con c = Mod_subst.subst_constant subst c
  and do_subst c = Mod_subst.subst_mps subst c
  and do_subst_gr gr = fst (subst_global subst gr) in
  let do_subst_ctx = List.Smart.map (RelDecl.map_constr do_subst) in
  let do_subst_context (grs,ctx) =
    List.Smart.map (Option.Smart.map do_subst_gr) grs,
    do_subst_ctx ctx in
  let do_subst_projs projs = List.Smart.map (fun (x, y, z) ->
    (x, y, Option.Smart.map do_subst_con z)) projs in
  { cl_univs = cl.cl_univs;
    cl_impl = do_subst_gr cl.cl_impl;
    cl_context = do_subst_context cl.cl_context;
    cl_props = do_subst_ctx cl.cl_props;
    cl_projs = do_subst_projs cl.cl_projs;
    cl_strict = cl.cl_strict;
    cl_unique = cl.cl_unique }

let discharge_class (_,cl) =
  let open CVars in
  let repl = Lib.replacement_context () in
  let rel_of_variable_context ctx = List.fold_right
    ( fun decl (ctx', subst) ->
        let decl' = decl |> NamedDecl.map_constr (substn_vars 1 subst) |> NamedDecl.to_rel_decl in
        (decl' :: ctx', NamedDecl.get_id decl :: subst)
    ) ctx ([], []) in
  let discharge_rel_context (subst, usubst) n rel =
    let rel = Context.Rel.map (Cooking.expmod_constr repl) rel in
    let fold decl (ctx, k) =
      let map c = subst_univs_level_constr usubst (substn_vars k subst c) in
      RelDecl.map_constr map decl :: ctx, succ k
    in
    let ctx, _ = List.fold_right fold rel ([], n) in
    ctx
  in
  let abs_context cl =
    let open GlobRef in
    match cl.cl_impl with
      | VarRef _ | ConstructRef _ -> assert false
      | ConstRef cst -> Lib.section_segment_of_constant cst
      | IndRef (ind,_) -> Lib.section_segment_of_mutual_inductive ind in
  let discharge_context ctx' subst (grs, ctx) =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let grs' =
      let newgrs = List.map (fun decl ->
                             match decl |> RelDecl.get_type |> EConstr.of_constr |> class_of_constr env sigma with
                             | None -> None
                             | Some (_, ((tc,_), _)) -> Some tc.cl_impl)
                            ctx'
      in
      grs @ newgrs
    in grs', discharge_rel_context subst 1 ctx @ ctx' in
  try
    let info = abs_context cl in
    let ctx = info.Section.abstr_ctx in
    let ctx, subst = rel_of_variable_context ctx in
    let usubst, cl_univs' = Lib.discharge_abstract_universe_context info cl.cl_univs in
    let context = discharge_context ctx (subst, usubst) cl.cl_context in
    let props = discharge_rel_context (subst, usubst) (succ (List.length (fst cl.cl_context))) cl.cl_props in
    let discharge_proj x = x in
    { cl_univs = cl_univs';
      cl_impl = cl.cl_impl;
      cl_context = context;
      cl_props = props;
      cl_projs = List.Smart.map discharge_proj cl.cl_projs;
      cl_strict = cl.cl_strict;
      cl_unique = cl.cl_unique
    }
  with Not_found -> (* not defined in the current section *)
    cl

let rebuild_class cl =
  try
    let cst = Tacred.evaluable_of_global_reference (Global.env ()) cl.cl_impl in
      set_typeclass_transparency cst false false; cl
  with e when CErrors.noncritical e -> cl

let class_input : typeclass -> obj =
  declare_object
    { (default_object "type classes state") with
      cache_function = cache_class;
      load_function = (fun _ -> cache_class);
      open_function = (fun _ -> cache_class);
      classify_function = (fun x -> Substitute x);
      discharge_function = (fun a -> Some (discharge_class a));
      rebuild_function = rebuild_class;
      subst_function = subst_class }

let add_class cl =
  Lib.add_anonymous_leaf (class_input cl)

let add_class env sigma cl =
  add_class cl;
  List.iter (fun (n, inst, body) ->
      match inst with
      | Some (Backward, info) ->
        (match body with
         | None -> CErrors.user_err Pp.(str "Non-definable projection can not be declared as a subinstance")
         | Some b -> declare_instance ~warn:true env sigma (Some info) false (GlobRef.ConstRef b))
      | _ -> ())
    cl.cl_projs

let intern_info {hint_priority;hint_pattern} =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let hint_pattern = Option.map (Constrintern.intern_constr_pattern env sigma) hint_pattern in
  {hint_priority;hint_pattern}

(** TODO: add subinstances *)
let existing_instance glob g info =
  let c = Nametab.global g in
  let info = Option.default Hints.empty_hint_info info in
  let info = intern_info info in
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let instance, _ = Typeops.type_of_global_in_context env c in
  let _, r = Term.decompose_prod_assum instance in
    match class_of_constr env sigma (EConstr.of_constr r) with
      | Some (_, ((tc,u), _)) -> add_instance (mk_instance tc info glob c)
      | None -> user_err ?loc:g.CAst.loc
                         ~hdr:"declare_instance"
                         (Pp.str "Constant does not build instances of a declared type class.")

(* Declare everything in the parameters as implicit, and the class instance as well *)

let type_ctx_instance ~program_mode env sigma ctx inst subst =
  let open Vars in
  let rec aux (sigma, subst, instctx) l = function
    decl :: ctx ->
      let t' = substl subst (RelDecl.get_type decl) in
      let (sigma, c'), l =
        match decl with
        | LocalAssum _ -> interp_casted_constr_evars ~program_mode env sigma (List.hd l) t', List.tl l
        | LocalDef (_,b,_) -> (sigma, substl subst b), l
      in
      let d = RelDecl.get_name decl, Some c', t' in
        aux (sigma, c' :: subst, d :: instctx) l ctx
    | [] -> sigma, subst
  in aux (sigma, subst, []) inst (List.rev ctx)

let id_of_class cl =
  let open GlobRef in
  match cl.cl_impl with
    | ConstRef kn -> Label.to_id @@ Constant.label kn
    | IndRef (kn,i) ->
        let mip = (Environ.lookup_mind kn (Global.env ())).Declarations.mind_packets in
          mip.(0).Declarations.mind_typename
    | _ -> assert false

let instance_hook info global ?hook cst =
  let info = intern_info info in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  declare_instance env sigma (Some info) (not global) cst;
  (match hook with Some h -> h cst | None -> ())

let declare_instance_constant info global impargs ?hook name udecl poly sigma term termtype =
  let kind = Decls.(IsDefinition Instance) in
  let entry = DeclareDef.prepare_definition
      ~poly sigma ~udecl ~types:(Some termtype) ~body:term in
  let scope = DeclareDef.Global Declare.ImportDefaultBehavior in
  let kn = DeclareDef.declare_definition ~name ~kind ~scope ~impargs entry in
  instance_hook info global ?hook kn

let do_declare_instance sigma ~global ~poly k u ctx ctx' pri udecl impargs subst name =
  let subst = List.fold_left2
      (fun subst' s decl -> if is_local_assum decl then s :: subst' else subst')
      [] subst (snd k.cl_context)
  in
  let (_, ty_constr) = instance_constructor (k,u) subst in
  let termtype = it_mkProd_or_LetIn ty_constr (ctx' @ ctx) in
  let sigma, entry = DeclareDef.prepare_parameter ~poly sigma ~udecl ~types:termtype in
  let cst = Declare.declare_constant ~name
      ~kind:Decls.(IsAssumption Logical) (Declare.ParameterEntry entry) in
  DeclareUniv.declare_univ_binders (GlobRef.ConstRef cst) (Evd.universe_binders sigma);
  let cst = (GlobRef.ConstRef cst) in
  Impargs.maybe_declare_manual_implicits false cst impargs;
  instance_hook pri global cst

let declare_instance_program env sigma ~global ~poly name pri imps udecl term termtype =
  let hook { DeclareDef.Hook.S.scope; dref; _ } =
    let cst = match dref with GlobRef.ConstRef kn -> kn | _ -> assert false in
    Impargs.declare_manual_implicits false dref imps;
    let pri = intern_info pri in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    declare_instance env sigma (Some pri) (not global) (GlobRef.ConstRef cst)
  in
  let obls, _, term, typ = RetrieveObl.retrieve_obligations env name sigma 0 term termtype in
  let hook = DeclareDef.Hook.make hook in
  let uctx = Evd.evar_universe_context sigma in
  let scope, kind = DeclareDef.Global Declare.ImportDefaultBehavior, Decls.Instance in
  let _ : DeclareObl.progress =
    Obligations.add_definition ~name ~term ~udecl ~scope ~poly ~kind ~hook typ ~uctx obls
  in ()

let declare_instance_open sigma ?hook ~tac ~global ~poly id pri impargs udecl ids term termtype =
  (* spiwack: it is hard to reorder the actions to do
     the pretyping after the proof has opened. As a
     consequence, we use the low-level primitives to code
     the refinement manually.*)
  let gls = List.rev (Evd.future_goals sigma) in
  let sigma = Evd.reset_future_goals sigma in
  let kind = Decls.(IsDefinition Instance) in
  let hook = DeclareDef.Hook.(make (fun { S.dref ; _ } -> instance_hook pri global ?hook dref)) in
  let info = Lemmas.Info.make ~hook ~kind () in
  (* XXX: We need to normalize the type, otherwise Admitted / Qed will fails!
     This is due to a bug in proof_global :( *)
  let termtype = Evarutil.nf_evar sigma termtype in
  let lemma = Lemmas.start_lemma ~name:id ~poly ~udecl ~info ~impargs sigma termtype in
  (* spiwack: I don't know what to do with the status here. *)
  let lemma =
    match term with
    | Some term ->
      let init_refine =
        Tacticals.New.tclTHENLIST [
          Refine.refine ~typecheck:false (fun sigma -> sigma, term);
          Proofview.Unsafe.tclNEWGOALS (CList.map Proofview.with_empty_state gls);
          Tactics.New.reduce_after_refine;
        ]
      in
      let lemma, _ = Lemmas.by init_refine lemma in
      lemma
    | None ->
      let lemma, _ = Lemmas.by (Tactics.auto_intros_tac ids) lemma in
      lemma
  in
  match tac with
  | Some tac ->
    let lemma, _ = Lemmas.by tac lemma in
    lemma
  | None ->
    lemma

let do_instance_subst_constructor_and_ty subst k u ctx =
  let subst =
    List.fold_left2 (fun subst' s decl ->
      if is_local_assum decl then s :: subst' else subst')
    [] subst (k.cl_props @ snd k.cl_context)
  in
  let (app, ty_constr) = instance_constructor (k,u) subst in
  let termtype = it_mkProd_or_LetIn ty_constr ctx in
  let term = it_mkLambda_or_LetIn (Option.get app) ctx in
  term, termtype

let do_instance_resolve_TC termtype sigma env =
  let sigma = Evarutil.nf_evar_map sigma in
  let sigma = Typeclasses.resolve_typeclasses ~filter:Typeclasses.no_goals_or_obligations ~fail:true env sigma in
  (* Try resolving fields that are typeclasses automatically. *)
  let sigma = Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars ~fail:false env sigma in
  let sigma = Evarutil.nf_evar_map_undefined sigma in
  (* Beware of this step, it is required as to minimize universes. *)
  let sigma = Evd.minimize_universes sigma in
  (* Check that the type is free of evars now. *)
  Pretyping.check_evars env sigma termtype;
  termtype, sigma

let do_instance_type_ctx_instance props k env' ctx' sigma ~program_mode subst =
  let get_id qid = CAst.make ?loc:qid.CAst.loc @@ qualid_basename qid in
  let props, rest =
    List.fold_left
      (fun (props, rest) decl ->
         if is_local_assum decl then
           try
             let is_id (id', _) = match RelDecl.get_name decl, get_id id' with
               | Name id, {CAst.v=id'} -> Id.equal id id'
               | Anonymous, _ -> false
             in
             let (loc_mid, c) = List.find is_id rest in
             let rest' = List.filter (fun v -> not (is_id v)) rest
             in
             let {CAst.loc;v=mid} = get_id loc_mid in
             List.iter (fun (n, _, x) ->
                 if Name.equal n (Name mid) then
                   Option.iter (fun x -> Dumpglob.add_glob ?loc (GlobRef.ConstRef x)) x) k.cl_projs;
             c :: props, rest'
           with Not_found ->
             ((CAst.make @@ CHole (None(* Some Evar_kinds.GoalEvar *), Namegen.IntroAnonymous, None)) :: props), rest
         else props, rest)
      ([], props) k.cl_props
  in
  match rest with
  | (n, _) :: _ ->
    unbound_method env' sigma k.cl_impl (get_id n)
  | _ ->
    let kcl_props = List.map (Termops.map_rel_decl of_constr) k.cl_props in
    let sigma, res =
      type_ctx_instance ~program_mode
        (push_rel_context ctx' env') sigma kcl_props props subst in
    res, sigma

let interp_props ~program_mode env' cty k u ctx ctx' subst sigma = function
  | (true, { CAst.v = CRecord fs; loc }) ->
    check_duplicate ?loc fs;
    let subst, sigma = do_instance_type_ctx_instance fs k env' ctx' sigma ~program_mode subst in
    let term, termtype =
      do_instance_subst_constructor_and_ty subst k u (ctx' @ ctx) in
    term, termtype, sigma
  | (_, term) ->
    let sigma, def =
      interp_casted_constr_evars ~program_mode env' sigma term cty in
    let termtype = it_mkProd_or_LetIn cty ctx in
    let term = it_mkLambda_or_LetIn def ctx in
    term, termtype, sigma

let do_instance_interactive env env' sigma ?hook ~tac ~global ~poly cty k u ctx ctx' pri decl imps subst id opt_props =
  let term, termtype, sigma = match opt_props with
    | Some props ->
      on_pi1 (fun x -> Some x)
        (interp_props ~program_mode:false env' cty k u ctx ctx' subst sigma props)
    | None ->
      let term, termtype =
        if List.is_empty k.cl_props then
          let term, termtype =
            do_instance_subst_constructor_and_ty subst k u (ctx' @ ctx) in
          Some term, termtype
        else
          None, it_mkProd_or_LetIn cty ctx
      in
      let termtype, sigma = do_instance_resolve_TC termtype sigma env in
      term, termtype, sigma
  in
  Flags.silently (fun () ->
      declare_instance_open sigma ?hook ~tac ~global ~poly
        id pri imps decl (List.map RelDecl.get_name ctx) term termtype)
    ()

let do_instance env env' sigma ?hook ~global ~poly cty k u ctx ctx' pri decl imps subst id props =
  let term, termtype, sigma =
    interp_props ~program_mode:false env' cty k u ctx ctx' subst sigma props
  in
  let termtype, sigma = do_instance_resolve_TC termtype sigma env in
  if Evd.has_undefined sigma then
    CErrors.user_err Pp.(str "Unsolved obligations remaining.")
  else
    declare_instance_constant pri global imps ?hook id decl poly sigma term termtype

let do_instance_program env env' sigma ?hook ~global ~poly cty k u ctx ctx' pri decl imps subst id opt_props =
  let term, termtype, sigma =
    match opt_props with
    | Some props ->
      interp_props ~program_mode:true env' cty k u ctx ctx' subst sigma props
    | None ->
      let subst, sigma =
        do_instance_type_ctx_instance [] k env' ctx' sigma ~program_mode:true subst in
      let term, termtype =
        do_instance_subst_constructor_and_ty subst k u (ctx' @ ctx) in
      term, termtype, sigma in
  let termtype, sigma = do_instance_resolve_TC termtype sigma env in
  if not (Evd.has_undefined sigma) && not (Option.is_empty opt_props) then
    declare_instance_constant pri global imps ?hook id decl poly sigma term termtype
  else
    declare_instance_program  env sigma ~global ~poly id pri imps decl term termtype

let interp_instance_context ~program_mode env ctx ~generalize pl tclass =
  let sigma, decl = Constrexpr_ops.interp_univ_decl_opt env pl in
  let tclass =
    if generalize then CAst.make @@ CGeneralization (Glob_term.MaxImplicit, Some AbsPi, tclass)
    else tclass
  in
  let sigma, (impls, ((env', ctx), imps)) = interp_context_evars ~program_mode env sigma ctx in
  let sigma, (c', imps') = interp_type_evars_impls ~program_mode ~impls env' sigma tclass in
  let imps = imps @ imps' in
  let ctx', c = decompose_prod_assum sigma c' in
  let ctx'' = ctx' @ ctx in
  let (k, u), args = Typeclasses.dest_class_app (push_rel_context ctx'' env) sigma c in
  let u_s = EInstance.kind sigma u in
  let cl = Typeclasses.typeclass_univ_instance (k, u_s) in
  let args = List.map of_constr args in
  let cl_context = List.map (Termops.map_rel_decl of_constr) (snd cl.cl_context) in
  let _, args =
    List.fold_right (fun decl (args, args') ->
        match decl with
        | LocalAssum _ -> (List.tl args, List.hd args :: args')
        | LocalDef (_,b,_) -> (args, Vars.substl args' b :: args'))
      cl_context (args, [])
  in
  let sigma = Evarutil.nf_evar_map sigma in
  let sigma = resolve_typeclasses ~filter:Typeclasses.all_evars ~fail:true env sigma in
  sigma, cl, u, c', ctx', ctx, imps, args, decl

let new_instance_common ~program_mode ~generalize env instid ctx cl =
  let ({CAst.loc;v=instid}, pl) = instid in
  let sigma, k, u, cty, ctx', ctx, imps, subst, decl =
    interp_instance_context ~program_mode env ~generalize ctx pl cl
  in
  (* The name generator should not be here *)
  let id =
    match instid with
    | Name id -> id
    | Anonymous ->
      let i = Nameops.add_suffix (id_of_class k) "_instance_0" in
      Namegen.next_global_ident_away i (Termops.vars_of_env env)
  in
  let env' = push_rel_context ctx env in
  id, env', sigma, k, u, cty, ctx', ctx, imps, subst, decl

let new_instance_interactive ?(global=false)
    ~poly instid ctx cl
    ?(generalize=true) ?(tac:unit Proofview.tactic option) ?hook
    pri opt_props =
  let env = Global.env() in
  let id, env', sigma, k, u, cty, ctx', ctx, imps, subst, decl =
    new_instance_common ~program_mode:false ~generalize env instid ctx cl in
  id, do_instance_interactive env env' sigma ?hook ~tac ~global ~poly
    cty k u ctx ctx' pri decl imps subst id opt_props

let new_instance_program ?(global=false)
    ~poly instid ctx cl opt_props
    ?(generalize=true) ?hook pri =
  let env = Global.env() in
  let id, env', sigma, k, u, cty, ctx', ctx, imps, subst, decl =
    new_instance_common ~program_mode:true ~generalize env instid ctx cl in
  do_instance_program env env' sigma ?hook ~global ~poly
    cty k u ctx ctx' pri decl imps subst id opt_props;
  id

let new_instance ?(global=false)
    ~poly instid ctx cl props
    ?(generalize=true) ?hook pri =
  let env = Global.env() in
  let id, env', sigma, k, u, cty, ctx', ctx, imps, subst, decl =
    new_instance_common ~program_mode:false ~generalize env instid ctx cl in
  do_instance env env' sigma ?hook ~global ~poly
    cty k u ctx ctx' pri decl imps subst id props;
  id

let declare_new_instance ?(global=false) ~program_mode ~poly instid ctx cl pri =
  let env = Global.env() in
  let ({CAst.loc;v=instid}, pl) = instid in
  let sigma, k, u, cty, ctx', ctx, imps, subst, decl =
    interp_instance_context ~program_mode ~generalize:false env ctx pl cl
  in
  do_declare_instance sigma ~global ~poly k u ctx ctx' pri decl imps subst instid

let refine_att =
  let open Attributes in
  let open Notations in
  attribute_of_list ["refine",single_key_parser ~name:"refine" ~key:"refine" ()] >>= function
  | None -> return false
  | Some () -> return true
