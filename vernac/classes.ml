(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

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

let warn_default_mode = CWarnings.create ~name:"class-declaration-default-mode" ~category:CWarnings.CoreCategories.automation
  ~default:CWarnings.Disabled
  Pp.(fun (gr, m) -> hov 2 (str "Using an inferred default mode: " ++ prlist_with_sep spc Hints.pp_hint_mode m ++
    spc () ++ str "for" ++ spc () ++ Printer.pr_global gr))

let set_typeclass_transparency ~locality c b =
  Hints.add_hints ~locality [typeclasses_db]
    (Hints.HintsTransparencyEntry (Hints.HintsReferences c, b))

let set_typeclass_transparency_com ~locality refs b =
  let refs = List.map
      (fun x -> Tacred.evaluable_of_global_reference
          (Global.env ())
          (Smartlocate.global_with_alias x))
      refs
  in
  set_typeclass_transparency ~locality refs b

let set_typeclass_mode ~locality c b =
  Hints.add_hints ~locality [typeclasses_db]
    (Hints.HintsModeEntry (c, b))

let add_instance_hint gr ~locality info =
  let inst = Hints.hint_globref gr in
     Flags.silently (fun () ->
       Hints.add_hints ~locality [typeclasses_db]
          (Hints.HintsResolveEntry
             [info, false, inst])) ()

(* short names without opening all Hints *)
type locality = Hints.hint_locality = Local | Export | SuperGlobal

type instance = {
  class_name : GlobRef.t;
  instance : GlobRef.t;
  info : Typeclasses.hint_info;
  (* Sections where the instance should be redeclared,
     None for discard, Some 0 for none. *)
  locality : Hints.hint_locality;
}

let add_instance_base inst =
  let locality =
    (* in a section, declare the hint as local
       since cache_instance will call add_instance_hint again;
       don't ask hints to take discharge into account itself *)
    if Global.sections_are_opened () then Local
    else inst.locality
  in
  add_instance_hint inst.instance ~locality inst.info

(*
 * instances persistent object
 *)
let perform_instance i =
  let i = { is_class = i.class_name; is_info = i.info; is_impl = i.instance } in
  Typeclasses.load_instance i

let cache_instance inst =
  perform_instance inst;
  add_instance_base inst

let load_instance _ inst = match inst.locality with
| Local -> assert false
| SuperGlobal -> perform_instance inst
| Export -> ()

let open_instance i inst = match inst.locality with
| Local -> assert false
| SuperGlobal -> perform_instance inst
| Export -> if Int.equal i 1 then perform_instance inst

let subst_instance (subst, inst) =
  { inst with
      class_name = fst (subst_global subst inst.class_name);
      instance = fst (subst_global subst inst.instance) }

let discharge_instance inst =
  match inst.locality with
  | Local -> None
  | SuperGlobal | Export ->
    assert (not (isVarRef inst.instance));
    Some inst

let classify_instance inst = match inst.locality with
| Local -> Dispose
| SuperGlobal | Export -> Substitute

let instance_input : instance -> obj =
  declare_object
    { (default_object "type classes instances state") with
      cache_function = cache_instance;
      load_function = load_instance;
      open_function = simple_open ~cat:Hints.hint_cat open_instance;
      classify_function = classify_instance;
      discharge_function = discharge_instance;
      subst_function = subst_instance }

module Event = struct
  type t =
    | NewClass of typeclass
    | NewInstance of instance
end

type observer = string

let observers = ref CString.Map.empty

let active_observers = Summary.ref ~name:"active typeclass observers" []

let register_observer ~name ?(override=false) o =
  if not override && CString.Map.mem name !observers then
    CErrors.anomaly Pp.(str "Typeclass observer " ++ str name ++ str " already registered.");
  observers := CString.Map.add name o !observers;
  name

let deactivate_observer name =
  active_observers := List.remove String.equal name !active_observers

let activate_observer name =
  assert (CString.Map.mem name !observers);
  deactivate_observer name;
  active_observers := name :: !active_observers

let observe event =
  List.iter (fun name -> (CString.Map.get name !observers) event) !active_observers

let add_instance cl info global impl =
  let () = match global with
    | Local -> ()
    | SuperGlobal ->
      if Lib.sections_are_opened () && isVarRef impl then
        CErrors.user_err (Pp.str "Cannot set Global an instance referring to a section variable.")
    | Export ->
      if Lib.sections_are_opened () && isVarRef impl then
        CErrors.user_err (Pp.str "The export attribute cannot be applied to an instance referring to a section variable.")
  in
  let i = {
    class_name = cl.cl_impl;
    info = info ;
    locality = global ;
    instance = impl;
  } in
  Lib.add_leaf (instance_input i);
  observe (Event.NewInstance { class_name = cl.cl_impl; instance = impl; info; locality = global })

let warning_not_a_class =
  CWarnings.create ~name:"not-a-class" (fun (n, ty) ->
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
      meth_const = c;
    }
  in
  let do_subst_projs projs = List.Smart.map do_subst_meth projs in
  { cl_univs = cl.cl_univs;
    cl_impl = do_subst_gr cl.cl_impl;
    cl_context = do_subst_ctx cl.cl_context;
    cl_trivial = cl.cl_trivial;
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
      cl_trivial = cl.cl_trivial;
      cl_props = props;
      cl_projs = List.Smart.map discharge_proj cl.cl_projs;
      cl_strict = cl.cl_strict;
      cl_unique = cl.cl_unique
    }
  with Not_found -> (* not defined in the current section *)
    cl

let class_input : typeclass -> obj =
  declare_object
    { (default_object "type classes state") with
      cache_function = cache_class;
      load_function = (fun _ -> cache_class);
      classify_function = (fun x -> Substitute);
      discharge_function = (fun a -> Some (discharge_class a));
      subst_function = subst_class;
    }

let add_class cl =
  Lib.add_leaf (class_input cl);
  observe (Event.NewClass cl)

let intern_info {hint_priority;hint_pattern} =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let hint_pattern = Option.map (Constrintern.intern_constr_pattern env sigma) hint_pattern in
  {hint_priority;hint_pattern}

(** TODO: add subinstances *)
let existing_instance ?loc glob c info =
  let info = Option.default Hints.empty_hint_info info in
  let info = intern_info info in
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let instance, _ = Typeops.type_of_global_in_context env c in
  let ctx, r = Term.decompose_prod_decls instance in
    match class_of_constr (Environ.push_rel_context ctx env) sigma (EConstr.of_constr r) with
      | Some (_, ((tc,u), _)) -> add_instance tc info glob c
      | None -> user_err ?loc (Pp.str "Constant does not build instances of a declared type class.")

type typeclass_in_univs = {
  clu_impl : GlobRef.t;
  clu_univs : EInstance.t;
  clu_context : EConstr.rel_context;
  clu_trivial : bool;
  clu_isstruct : Structures.Structure.t option;
  clu_props : EConstr.rel_context;
  clu_projs : class_method list;
}

(* Declare everything in the parameters as implicit, and the class instance as well *)

let type_ctx_instance ~program_mode env sigma ctx inst subst =
  let open Vars in
  let rec aux (sigma, subst) l ctx = match ctx, l with
    | LocalAssum _ :: _, [] | [], _ :: _ -> assert false
    | LocalAssum (_,t) :: ctx, c :: l ->
      let t' = substl subst t in
      let (sigma, c') =
        interp_casted_constr_evars ~program_mode env sigma c t'
      in
      aux (sigma, c' :: subst) l ctx
    | LocalDef (_,b,_) :: ctx, l ->
      let c' = substl subst b in
      aux (sigma, c' :: subst) l ctx
    | [], [] -> sigma, subst
  in
  aux (sigma, subst) inst (List.rev ctx)

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

let instance_type cl args =
  let lenpars = List.count is_local_assum cl.clu_context in
  let pars = List.firstn lenpars args in
  applist (mkRef (cl.clu_impl,cl.clu_univs), pars)

let do_declare_instance sigma ~locality ~poly k ctx ctx' pri udecl impargs subst name =
  let subst = List.fold_left2
      (fun subst' s decl -> if is_local_assum decl then s :: subst' else subst')
      [] subst k.clu_context
  in
  let ty_constr = instance_type k subst in
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
  let obls, _, body, typ = RetrieveObl.retrieve_obligations env name sigma 0 term termtype in
  let hook = Declare.Hook.make hook in
  let uctx = Evd.ustate sigma in
  let kind = Decls.IsDefinition Decls.Instance in
  let cinfo = Declare.CInfo.make ~name ~typ ~impargs () in
  let info = Declare.Info.make ~udecl ~poly ~kind ~hook () in
  let pm, _ =
    Declare.Obls.add_definition ~pm ~info ~cinfo ~opaque:false ~uctx ~body obls
  in pm

let declare_instance_open sigma ?hook ~tac ~locality ~poly id pri impargs udecl ids term termtype =
  (* spiwack: it is hard to reorder the actions to do
     the pretyping after the proof has opened. As a
     consequence, we use the low-level primitives to code
     the refinement manually.*)
  let future_goals, sigma = Evd.pop_future_goals sigma in
  let gls = List.rev (Evd.FutureGoals.comb future_goals) in
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
          Tactics.reduce_after_refine;
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

let instance_constructor cl args =
  match cl.clu_isstruct with
  | Some s ->
    applist (mkConstructUi ((s.name,cl.clu_univs), 1), args)
  | None ->
    List.last args

let do_instance_subst_constructor_and_ty subst k ctx =
  let subst =
    List.fold_left2 (fun subst' s decl ->
      if is_local_assum decl then s :: subst' else subst')
    [] subst (k.clu_props @ k.clu_context)
  in
  let ty_constr = instance_type k subst in
  let app = instance_constructor k subst in
  let termtype = it_mkProd_or_LetIn ty_constr ctx in
  let term = it_mkLambda_or_LetIn app ctx in
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
             let opt_proj = List.find_opt (fun m -> Name.equal m.meth_name (Name mid)) k.clu_projs in
             opt_proj |> Option.iter (fun x ->
                 x.meth_const |> Option.iter (fun x -> Dumpglob.add_glob ?loc (GlobRef.ConstRef x)));
             c :: props, rest'
           with Not_found ->
             ((CAst.make @@ CHole (None)) :: props), rest
         else props, rest)
      ([], props) k.clu_props
  in
  match rest with
  | (n, _) :: _ ->
    unbound_method env' sigma k.clu_impl (get_id n)
  | [] ->
    let sigma, res =
      type_ctx_instance ~program_mode
        (push_rel_context ctx' env') sigma k.clu_props props subst in
    res, sigma

let interp_props ~program_mode env' cty k ctx ctx' subst sigma = function
  | (true, { CAst.v = CRecord fs; loc }) ->
    check_duplicate ?loc fs;
    let subst, sigma = do_instance_type_ctx_instance fs k env' ctx' sigma ~program_mode subst in
    let term, termtype =
      do_instance_subst_constructor_and_ty subst k (ctx' @ ctx) in
    term, termtype, sigma
  | (_, term) ->
    let sigma, def =
      interp_casted_constr_evars ~program_mode env' sigma term cty in
    let termtype = it_mkProd_or_LetIn cty ctx in
    let term = it_mkLambda_or_LetIn def ctx in
    term, termtype, sigma

let do_instance_interactive env env' sigma ?hook ~tac ~locality ~poly cty k ctx ctx' pri decl imps subst id opt_props =
  let term, termtype, sigma = match opt_props with
    | Some props ->
      on_pi1 (fun x -> Some x)
        (interp_props ~program_mode:false env' cty k ctx ctx' subst sigma props)
    | None ->
      let term, termtype =
        if k.clu_trivial then
          let term, termtype =
            do_instance_subst_constructor_and_ty subst k (ctx' @ ctx) in
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

let do_instance env env' sigma ?hook ~locality ~poly cty k ctx ctx' pri decl imps subst id props =
  let term, termtype, sigma =
    interp_props ~program_mode:false env' cty k ctx ctx' subst sigma props
  in
  let termtype, sigma = do_instance_resolve_TC termtype sigma env in
  Pretyping.check_evars_are_solved ~program_mode:false env sigma;
  declare_instance_constant pri locality imps ?hook id decl poly sigma term termtype

let do_instance_program ~pm env env' sigma ?hook ~locality ~poly cty k ctx ctx' pri decl imps subst id opt_props =
  let term, termtype, sigma =
    match opt_props with
    | Some props ->
      interp_props ~program_mode:true env' cty k ctx ctx' subst sigma props
    | None ->
      let subst, sigma =
        do_instance_type_ctx_instance [] k env' ctx' sigma ~program_mode:true subst in
      let term, termtype =
        do_instance_subst_constructor_and_ty subst k (ctx' @ ctx) in
      term, termtype, sigma in
  let termtype, sigma = do_instance_resolve_TC termtype sigma env in
  if not (Evd.has_undefined sigma) && not (Option.is_empty opt_props) then
    let () = declare_instance_constant pri locality imps ?hook id decl poly sigma term termtype in
    pm
  else
    declare_instance_program pm env sigma ~locality ~poly id pri imps decl term termtype

let typeclass_univ_instance (cl, u) =
  assert (UVars.eq_sizes (UVars.AbstractContext.size cl.cl_univs) (EInstance.length u));
  let subst_ctx c = Context.Rel.map (Vars.subst_instance_constr u) (EConstr.of_rel_context c) in
  let clu_isstruct = match cl.cl_impl with
    | ConstRef _ -> None
    | ConstructRef _ | VarRef _ -> assert false
    | IndRef ind -> match Structures.Structure.find ind with
      | exception Not_found -> None
      | s -> Some s
  in
  { clu_impl = cl.cl_impl;
    clu_univs = u;
    clu_context = subst_ctx cl.cl_context;
    clu_props = subst_ctx cl.cl_props;
    clu_isstruct;
    clu_trivial = cl.cl_trivial;
    clu_projs = cl.cl_projs;
  }

let interp_instance_context ~program_mode env ctx pl tclass =
  let sigma, decl = interp_univ_decl_opt env pl in
  let sigma, (impls, ((env', ctx), imps)) = interp_context_evars ~program_mode env sigma ctx in
  let flags = Pretyping.{ all_no_fail_flags with program_mode } in
  let sigma, (c', imps') = interp_type_evars_impls ~flags ~impls env' sigma tclass in
  let imps = imps @ imps' in
  let ctx', c = decompose_prod_decls sigma c' in
  let ctx'' = ctx' @ ctx in
  let (k, u), args = Typeclasses.dest_class_app (push_rel_context ctx'' env) sigma c in
  let cl = typeclass_univ_instance (k, u) in
  let args = List.map of_constr args in
  let _, args =
    List.fold_right (fun decl (args, args') ->
        match decl with
        | LocalAssum _ -> (List.tl args, List.hd args :: args')
        | LocalDef (_,b,_) -> (args, Vars.substl args' b :: args'))
      cl.clu_context (args, [])
  in
  let sigma = Evarutil.nf_evar_map sigma in
  let sigma = resolve_typeclasses ~filter:Typeclasses.all_evars ~fail:true env sigma in
  sigma, cl, u, c', ctx', ctx, imps, args, decl

let id_of_class env ref =
  let open GlobRef in
  match ref with
    | ConstRef kn -> Label.to_id @@ Constant.label kn
    | IndRef (kn,i) ->
        let mip = (Environ.lookup_mind kn env).Declarations.mind_packets in
          mip.(0).Declarations.mind_typename
    | _ -> assert false

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
      let i = Nameops.add_suffix (id_of_class env k.clu_impl) "_instance_0" in
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
    cty k ctx ctx' pri decl imps subst id opt_props

let new_instance_program ~locality ~pm ~poly instid ctx cl opt_props ?hook pri =
  let env = Global.env() in
  let id, env', sigma, k, u, cty, ctx', ctx, imps, subst, decl =
    new_instance_common ~program_mode:true env instid ctx cl in
  let pm =
    do_instance_program ~pm env env' sigma ?hook ~locality ~poly
      cty k ctx ctx' pri decl imps subst id opt_props in
  pm, id

let new_instance ~locality ~poly instid ctx cl props ?hook pri =
  let env = Global.env() in
  let id, env', sigma, k, u, cty, ctx', ctx, imps, subst, decl =
    new_instance_common ~program_mode:false env instid ctx cl in
  do_instance env env' sigma ?hook ~locality ~poly
    cty k ctx ctx' pri decl imps subst id props;
  id

let declare_new_instance ~locality ~program_mode ~poly instid ctx cl pri =
  let env = Global.env() in
  let ({CAst.loc;v=instid}, pl) = instid in
  let sigma, k, u, cty, ctx', ctx, imps, subst, decl =
    interp_instance_context ~program_mode env ctx pl cl
  in
  do_declare_instance sigma ~locality ~poly k ctx ctx' pri decl imps subst instid

let refine_att =
  let open Attributes in
  let open Notations in
  attribute_of_list ["refine",single_key_parser ~name:"refine" ~key:"refine" ()] >>= function
  | None -> return false
  | Some () -> return true

module Internal = struct
  let add_instance = add_instance
end
