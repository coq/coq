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
(*i*)

let set_typeclass_transparency ~locality c b =
  Hints.add_hints ~locality [typeclasses_db]
    (Hints.HintsTransparencyEntry (Hints.HintsReferences c, b))

let warn_deprecated_tc_transparency_without_locality =
  CWarnings.create ~name:"deprecated-typeclasses-transparency-without-locality" ~category:"deprecated"
    Pp.(fun () -> strbrk
  "The default value for Typeclasses Opaque and Typeclasses \
   Transparent locality is currently \"local\" in a section and \
   \"global\" otherwise, but is scheduled to change in a future \
   release. For the time being, adding typeclass transparency hints outside of \
   sections without specifying an explicit locality attribute is \
   therefore deprecated. It is recommended to use \"export\" whenever \
   possible. Use the attributes #[local], #[global] and #[export] \
   depending on your choice. For example: \"#[export] Typeclasses Transparent foo.\". \
   This is supported since Coq 8.15.")

let default_tc_transparency_locality () =
  if Global.sections_are_opened () then Hints.Local
  else
    let () = warn_deprecated_tc_transparency_without_locality () in
    Hints.SuperGlobal

let tc_transparency_locality = Attributes.hint_locality ~default:default_tc_transparency_locality

let set_typeclass_transparency_com ~locality refs b =
  let refs = List.map
      (fun x -> Tacred.evaluable_of_global_reference
          (Global.env ())
          (Smartlocate.global_with_alias x))
      refs
  in
  set_typeclass_transparency ~locality refs b

let add_instance_hint inst path ~locality info =
     Flags.silently (fun () ->
       Hints.add_hints ~locality [typeclasses_db]
          (Hints.HintsResolveEntry
             [info, false, Hints.PathHints path, inst])) ()

(* short names without opening all Hints *)
type locality = Hints.hint_locality = Local | Export | SuperGlobal

type instance_obj = {
  inst_class : GlobRef.t;
  inst_info: hint_info;
  (* Sections where the instance should be redeclared,
     None for discard, Some 0 for none. *)
  inst_global: Hints.hint_locality;
  inst_impl: GlobRef.t;
}

let add_instance_base inst =
  let locality = match inst.inst_global with
  | Local -> Local
  | SuperGlobal ->
    (* i.e. in a section, declare the hint as local since discharge is managed
       by rebuild_instance which calls again add_instance_hint; don't ask hints
       to take discharge into account itself *)
    if Global.sections_are_opened () then Local
    else SuperGlobal
  | Export ->
    (* Same as above for export *)
    if Global.sections_are_opened () then Local
    else Export
  in
  add_instance_hint (Hints.hint_globref inst.inst_impl) [inst.inst_impl] ~locality
    inst.inst_info

(*
 * instances persistent object
 *)
let perform_instance i =
  let i = { is_class = i.inst_class; is_info = i.inst_info; is_impl = i.inst_impl } in
  Typeclasses.load_instance i

let cache_instance inst = perform_instance inst

let load_instance _ inst = match inst.inst_global with
| Local -> assert false
| SuperGlobal -> perform_instance inst
| Export -> ()

let open_instance i inst = match inst.inst_global with
| Local -> assert false
| SuperGlobal -> perform_instance inst
| Export -> if Int.equal i 1 then perform_instance inst

let subst_instance (subst, inst) =
  { inst with
      inst_class = fst (subst_global subst inst.inst_class);
      inst_impl = fst (subst_global subst inst.inst_impl) }

let discharge_instance inst =
  match inst.inst_global with
  | Local -> None
  | SuperGlobal | Export ->
    assert (not (isVarRef inst.inst_impl));
    Some inst

let rebuild_instance inst =
  add_instance_base inst;
  inst

let classify_instance inst = match inst.inst_global with
| Local -> Dispose
| SuperGlobal | Export -> Substitute

let instance_input : instance_obj -> obj =
  declare_object
    { (default_object "type classes instances state") with
      cache_function = cache_instance;
      load_function = load_instance;
      open_function = simple_open ~cat:Hints.hint_cat open_instance;
      classify_function = classify_instance;
      discharge_function = discharge_instance;
      rebuild_function = rebuild_instance;
      subst_function = subst_instance }

let warn_deprecated_instance_without_locality =
  let open Pp in
  CWarnings.create ~name:"deprecated-instance-without-locality" ~category:"deprecated"
    (fun () -> strbrk "The default value for instance locality is currently \
    \"local\" in a section and \"global\" otherwise, but is scheduled to change \
    in a future release. For the time being, adding instances outside of sections \
    without specifying an explicit locality attribute is therefore deprecated. It is \
    recommended to use \"export\" whenever possible. Use the attributes \
    #[local], #[global] and #[export] depending on your choice. For example: \
    \"#[export] Instance Foo : Bar := baz.\"")

let default_locality () =
  if Global.sections_are_opened () then Local
  else
    let () = warn_deprecated_instance_without_locality () in
    SuperGlobal

let instance_locality =
  Attributes.hint_locality ~default:default_locality

let add_instance cl info global impl =
  let () = match global with
    | Local -> ()
    | SuperGlobal ->
      if Global.sections_are_opened () && isVarRef impl then
        CErrors.user_err (Pp.str "Cannot set Global an instance referring to a section variable.")
    | Export ->
      if Global.sections_are_opened () && isVarRef impl then
        CErrors.user_err (Pp.str "The export attribute cannot be applied to an instance referring to a section variable.")
  in
  let i = {
    inst_class = cl.cl_impl;
    inst_info = info ;
    inst_global = global ;
    inst_impl = impl;
  } in
  Lib.add_leaf (instance_input i);
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
    add_instance tc info local glob
  | None -> if warn then warning_not_a_class (glob, ty)

(*
 * classes persistent object
 *)

let cache_class c = load_class c

let subst_class (subst,cl) =
  let do_subst_con c = Mod_subst.subst_constant subst c
  and do_subst c = Mod_subst.subst_mps subst c
  and do_subst_gr gr = fst (subst_global subst gr) in
  let do_subst_ctx = List.Smart.map (RelDecl.map_constr do_subst) in
  let do_subst_meth m =
    let c = Option.Smart.map do_subst_con m.meth_const in
    if c == m.meth_const then m
    else
    {
      meth_name = m.meth_name;
      meth_info = m.meth_info;
      meth_const = c;
    }
  in
  let do_subst_projs projs = List.Smart.map do_subst_meth projs in
  { cl_univs = cl.cl_univs;
    cl_impl = do_subst_gr cl.cl_impl;
    cl_context = do_subst_ctx cl.cl_context;
    cl_props = do_subst_ctx cl.cl_props;
    cl_projs = do_subst_projs cl.cl_projs;
    cl_strict = cl.cl_strict;
    cl_unique = cl.cl_unique }

let discharge_class cl =
  try
    let info = Lib.section_segment_of_reference cl.cl_impl in
    let info, _, cl_univs' = Cooking.lift_poly_univs info cl.cl_univs in
    let nprops = List.length cl.cl_props in
    let props, context = List.chop nprops (Discharge.cook_rel_context info (cl.cl_props @ cl.cl_context)) in
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
      set_typeclass_transparency ~locality:Hints.Local [cst] false; cl
  with e when CErrors.noncritical e -> cl

let class_input : typeclass -> obj =
  declare_object
    { (default_object "type classes state") with
      cache_function = cache_class;
      load_function = (fun _ -> cache_class);
      classify_function = (fun x -> Substitute);
      discharge_function = (fun a -> Some (discharge_class a));
      rebuild_function = rebuild_class;
      subst_function = subst_class }

let add_class cl =
  Lib.add_leaf (class_input cl)

let add_class env sigma cl =
  add_class cl;
  List.iter (fun m ->
      match m.meth_info with
      | Some info ->
        (match m.meth_const with
         | None -> CErrors.user_err Pp.(str "Non-definable projection can not be declared as a subinstance")
         | Some b -> declare_instance ~warn:true env sigma (Some info) SuperGlobal (GlobRef.ConstRef b))
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
  let ctx, r = Term.decompose_prod_assum instance in
    match class_of_constr (Environ.push_rel_context ctx env) sigma (EConstr.of_constr r) with
      | Some (_, ((tc,u), _)) -> add_instance tc info glob c
      | None -> user_err ?loc:g.CAst.loc
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
  declare_instance env sigma (Some info) global cst;
  (match hook with Some h -> h cst | None -> ())

let declare_instance_constant iinfo global impargs ?hook name udecl poly sigma term termtype =
  let kind = Decls.(IsDefinition Instance) in
  let cinfo = Declare.CInfo.make ~name ~impargs ~typ:(Some termtype) () in
  let info = Declare.Info.make ~kind ~poly ~udecl () in
  let kn = Declare.declare_definition ~cinfo ~info ~opaque:false ~body:term sigma in
  instance_hook iinfo global ?hook kn

let do_declare_instance sigma ~locality ~poly k u ctx ctx' pri udecl impargs subst name =
  let subst = List.fold_left2
      (fun subst' s decl -> if is_local_assum decl then s :: subst' else subst')
      [] subst k.cl_context
  in
  let (_, ty_constr) = instance_constructor (k,u) subst in
  let termtype = it_mkProd_or_LetIn ty_constr (ctx' @ ctx) in
  let sigma, entry = Declare.prepare_parameter ~poly sigma ~udecl ~types:termtype in
  let cst = Declare.declare_constant ~name
      ~kind:Decls.(IsAssumption Logical) (Declare.ParameterEntry entry) in
  let cst = (GlobRef.ConstRef cst) in
  Impargs.maybe_declare_manual_implicits false cst impargs;
  instance_hook pri locality cst

let declare_instance_program pm env sigma ~locality ~poly name pri impargs udecl term termtype =
  let hook { Declare.Hook.S.scope; dref; _ } =
    let cst = match dref with GlobRef.ConstRef kn -> kn | _ -> assert false in
    let pri = intern_info pri in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    declare_instance env sigma (Some pri) locality (GlobRef.ConstRef cst)
  in
  let obls, _, term, typ = RetrieveObl.retrieve_obligations env name sigma 0 term termtype in
  let hook = Declare.Hook.make hook in
  let uctx = Evd.evar_universe_context sigma in
  let kind = Decls.IsDefinition Decls.Instance in
  let cinfo = Declare.CInfo.make ~name ~typ ~impargs () in
  let info = Declare.Info.make  ~udecl ~poly ~kind ~hook () in
  let pm, _ =
    Declare.Obls.add_definition ~pm ~cinfo ~info ~term ~uctx obls
  in pm

let declare_instance_open sigma ?hook ~tac ~locality ~poly id pri impargs udecl ids term termtype =
  (* spiwack: it is hard to reorder the actions to do
     the pretyping after the proof has opened. As a
     consequence, we use the low-level primitives to code
     the refinement manually.*)
  let future_goals, sigma = Evd.pop_future_goals sigma in
  let gls = List.rev future_goals.Evd.FutureGoals.comb in
  let sigma = Evd.push_future_goals sigma in
  let kind = Decls.(IsDefinition Instance) in
  let hook = Declare.Hook.(make (fun { S.dref ; _ } -> instance_hook pri locality ?hook dref)) in
  let info = Declare.Info.make ~hook ~kind ~udecl ~poly () in
  (* XXX: We need to normalize the type, otherwise Admitted / Qed will fails!
     This is due to a bug in proof_global :( *)
  let termtype = Evarutil.nf_evar sigma termtype in
  let cinfo = Declare.CInfo.make ~name:id ~impargs ~typ:termtype () in
  let lemma = Declare.Proof.start ~cinfo ~info sigma in
  (* spiwack: I don't know what to do with the status here. *)
  let lemma =
    match term with
    | Some term ->
      let init_refine =
        Tacticals.tclTHENLIST [
          Refine.refine ~typecheck:false (fun sigma -> sigma, term);
          Proofview.Unsafe.tclNEWGOALS (CList.map Proofview.with_empty_state gls);
          Tactics.New.reduce_after_refine;
        ]
      in
      let lemma, _ = Declare.Proof.by init_refine lemma in
      lemma
    | None ->
      let lemma, _ = Declare.Proof.by (Tactics.auto_intros_tac ids) lemma in
      lemma
  in
  match tac with
  | Some tac ->
    let lemma, _ = Declare.Proof.by tac lemma in
    lemma
  | None ->
    lemma

let do_instance_subst_constructor_and_ty subst k u ctx =
  let subst =
    List.fold_left2 (fun subst' s decl ->
      if is_local_assum decl then s :: subst' else subst')
    [] subst (k.cl_props @ k.cl_context)
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
             List.iter (fun m ->
                 if Name.equal m.meth_name (Name mid) then
                   Option.iter (fun x -> Dumpglob.add_glob ?loc (GlobRef.ConstRef x)) m.meth_const) k.cl_projs;
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

let do_instance_interactive env env' sigma ?hook ~tac ~locality ~poly cty k u ctx ctx' pri decl imps subst id opt_props =
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
      declare_instance_open sigma ?hook ~tac ~locality ~poly
        id pri imps decl (List.map RelDecl.get_name ctx) term termtype)
    ()

let do_instance env env' sigma ?hook ~locality ~poly cty k u ctx ctx' pri decl imps subst id props =
  let term, termtype, sigma =
    interp_props ~program_mode:false env' cty k u ctx ctx' subst sigma props
  in
  let termtype, sigma = do_instance_resolve_TC termtype sigma env in
  Pretyping.check_evars_are_solved ~program_mode:false env sigma;
  declare_instance_constant pri locality imps ?hook id decl poly sigma term termtype

let do_instance_program ~pm env env' sigma ?hook ~locality ~poly cty k u ctx ctx' pri decl imps subst id opt_props =
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
    let () = declare_instance_constant pri locality imps ?hook id decl poly sigma term termtype in
    pm
  else
    declare_instance_program pm env sigma ~locality ~poly id pri imps decl term termtype

let interp_instance_context ~program_mode env ctx pl tclass =
  let sigma, decl = interp_univ_decl_opt env pl in
  let sigma, (impls, ((env', ctx), imps)) = interp_context_evars ~program_mode env sigma ctx in
  let flags = Pretyping.{ all_no_fail_flags with program_mode } in
  let sigma, (c', imps') = interp_type_evars_impls ~flags ~impls env' sigma tclass in
  let imps = imps @ imps' in
  let ctx', c = decompose_prod_assum sigma c' in
  let ctx'' = ctx' @ ctx in
  let (k, u), args = Typeclasses.dest_class_app (push_rel_context ctx'' env) sigma c in
  let u_s = EInstance.kind sigma u in
  let cl = Typeclasses.typeclass_univ_instance (k, u_s) in
  let args = List.map of_constr args in
  let cl_context = List.map (Termops.map_rel_decl of_constr) cl.cl_context in
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

let new_instance_common ~program_mode env instid ctx cl =
  let ({CAst.loc;v=instid}, pl) = instid in
  let sigma, k, u, cty, ctx', ctx, imps, subst, decl =
    interp_instance_context ~program_mode env ctx pl cl
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

let new_instance_interactive ~locality ~poly instid ctx cl
    ?(tac:unit Proofview.tactic option) ?hook
    pri opt_props =
  let env = Global.env() in
  let id, env', sigma, k, u, cty, ctx', ctx, imps, subst, decl =
    new_instance_common ~program_mode:false env instid ctx cl in
  id, do_instance_interactive env env' sigma ?hook ~tac ~locality ~poly
    cty k u ctx ctx' pri decl imps subst id opt_props

let new_instance_program ~locality ~pm ~poly instid ctx cl opt_props ?hook pri =
  let env = Global.env() in
  let id, env', sigma, k, u, cty, ctx', ctx, imps, subst, decl =
    new_instance_common ~program_mode:true env instid ctx cl in
  let pm =
    do_instance_program ~pm env env' sigma ?hook ~locality ~poly
      cty k u ctx ctx' pri decl imps subst id opt_props in
  pm, id

let new_instance ~locality ~poly instid ctx cl props ?hook pri =
  let env = Global.env() in
  let id, env', sigma, k, u, cty, ctx', ctx, imps, subst, decl =
    new_instance_common ~program_mode:false env instid ctx cl in
  do_instance env env' sigma ?hook ~locality ~poly
    cty k u ctx ctx' pri decl imps subst id props;
  id

let declare_new_instance ~locality ~program_mode ~poly instid ctx cl pri =
  let env = Global.env() in
  let ({CAst.loc;v=instid}, pl) = instid in
  let sigma, k, u, cty, ctx', ctx, imps, subst, decl =
    interp_instance_context ~program_mode env ctx pl cl
  in
  do_declare_instance sigma ~locality ~poly k u ctx ctx' pri decl imps subst instid

let refine_att =
  let open Attributes in
  let open Notations in
  attribute_of_list ["refine",single_key_parser ~name:"refine" ~key:"refine" ()] >>= function
  | None -> return false
  | Some () -> return true

module Internal =
struct
let add_instance cl info glob r =
  let glob = if glob then SuperGlobal else Local in
  add_instance cl info glob r
end
