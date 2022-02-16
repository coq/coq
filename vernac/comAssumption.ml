(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Vars
open Names
open Context
open Constrintern
open Impargs
open Pretyping

module RelDecl = Context.Rel.Declaration
(* 2| Variable/Hypothesis/Parameter/Axiom declarations *)

let declare_variable is_coe ~kind typ univs imps impl {CAst.v=name} =
  let kind = Decls.IsAssumption kind in
  let () = Declare.declare_variable ~name ~kind ~typ ~impl ~univs in
  let () = Declare.assumption_message name in
  let r = GlobRef.VarRef name in
  let () = maybe_declare_manual_implicits true r imps in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let () = Classes.declare_instance env sigma None Hints.Local r in
  let () = if is_coe then ComCoercion.try_add_new_coercion r ~local:true ~poly:false ~nonuniform:false ~reversible:true in
  ()

let instance_of_univ_entry = function
  | UState.Polymorphic_entry univs -> Univ.UContext.instance univs
  | UState.Monomorphic_entry _ -> Univ.Instance.empty

let declare_axiom is_coe ~poly ~local ~kind typ (univs, ubinders) imps nl {CAst.v=name} =
  let do_instance = let open Decls in match kind with
  | Context -> true
    (* The typeclass behaviour of Variable and Context doesn't depend
       on section status *)
  | Definitional | Logical | Conjectural -> false
  in
  let inl = let open Declaremods in match nl with
    | NoInline -> None
    | DefaultInline -> Some (Flags.get_inline_level())
    | InlineAt i -> Some i
  in
  let kind = Decls.IsAssumption kind in
  let entry = Declare.parameter_entry ~univs:(univs, ubinders) ?inline:inl typ in
  let decl = Declare.ParameterEntry entry in
  let kn = Declare.declare_constant ~name ~local ~kind decl in
  let gr = GlobRef.ConstRef kn in
  let () = maybe_declare_manual_implicits false gr imps in
  let () = Declare.assumption_message name in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let () = if do_instance then Classes.declare_instance env sigma None Hints.SuperGlobal gr in
  let local = match local with
    | Locality.ImportNeedQualified -> true
    | Locality.ImportDefaultBehavior -> false
  in
  let () = if is_coe then ComCoercion.try_add_new_coercion gr ~local ~poly ~nonuniform:false ~reversible:true in
  let inst = instance_of_univ_entry univs in
  (gr,inst)

let interp_assumption ~program_mode env sigma impl_env bl c =
  let flags = { Pretyping.all_no_fail_flags with program_mode } in
  let sigma, (impls, ((env_bl, ctx), impls1)) = interp_context_evars ~program_mode ~impl_env env sigma bl in
  let sigma, (ty, impls2) = interp_type_evars_impls ~flags env_bl sigma ~impls c in
  let ty = EConstr.it_mkProd_or_LetIn ty ctx in
  sigma, ty, impls1@impls2

let empty_poly_univ_entry = UState.Polymorphic_entry Univ.UContext.empty, UnivNames.empty_binders
let empty_mono_univ_entry = UState.Monomorphic_entry Univ.ContextSet.empty, UnivNames.empty_binders
let empty_univ_entry ~poly = if poly then empty_poly_univ_entry else empty_mono_univ_entry

(* When declarations are monomorphic (which is always the case in
   sections, even when universes are treated as polymorphic variables)
   the universe constraints and universe names are declared with the
   first declaration only. *)

let clear_univs scope univ =
  match scope, univ with
  | Locality.Global _, (UState.Polymorphic_entry _, _ as univs) -> univs
  | _, (UState.Monomorphic_entry _, _) -> empty_univ_entry ~poly:false
  | Locality.Discharge, (UState.Polymorphic_entry _, _) -> empty_univ_entry ~poly:true

let declare_assumptions ~poly ~scope ~kind univs nl l =
  let _, _ = List.fold_left (fun (subst,univs) ((is_coe,idl),typ,imps) ->
      (* NB: here univs are ignored when scope=Discharge *)
      let typ = replace_vars subst typ in
      let univs,subst' =
        List.fold_left_map (fun univs id ->
            let refu = match scope with
              | Locality.Discharge ->
                declare_variable is_coe ~kind typ univs imps Glob_term.Explicit id;
                GlobRef.VarRef id.CAst.v, Univ.Instance.empty
              | Locality.Global local ->
                declare_axiom is_coe ~local ~poly ~kind typ univs imps nl id
            in
            clear_univs scope univs, (id.CAst.v, Constr.mkRef refu))
          univs idl
      in
      subst'@subst, clear_univs scope univs)
      ([], univs) l
  in
  ()

let maybe_error_many_udecls = function
  | ({CAst.loc;v=id}, Some _) ->
    user_err ?loc
      Pp.(str "When declaring multiple axioms in one command, " ++
          str "only the first is allowed a universe binder " ++
          str "(which will be shared by the whole block).")
  | (_, None) -> ()

let process_assumptions_udecls ~scope l =
  let udecl, first_id = match l with
    | (coe, ((id, udecl)::rest, c))::rest' ->
      List.iter maybe_error_many_udecls rest;
      List.iter (fun (coe, (idl, c)) -> List.iter maybe_error_many_udecls idl) rest';
      udecl, id
    | (_, ([], _))::_ | [] -> assert false
  in
  let () = match scope, udecl with
    | Locality.Discharge, Some _ ->
      let loc = first_id.CAst.loc in
      let msg = Pp.str "Section variables cannot be polymorphic." in
      user_err ?loc  msg
    | _ -> ()
  in
  udecl, List.map (fun (coe, (idl, c)) -> coe, (List.map fst idl, c)) l

let do_assumptions ~program_mode ~poly ~scope ~kind nl l =
  let open Context.Named.Declaration in
  let env = Global.env () in
  let udecl, l = process_assumptions_udecls ~scope l in
  let sigma, udecl = interp_univ_decl_opt env udecl in
  let l =
    if poly then
      (* Separate declarations so that A B : Type puts A and B in different levels. *)
      List.fold_right (fun (is_coe,(idl,c)) acc ->
        List.fold_right (fun id acc ->
          (is_coe, ([id], c)) :: acc) idl acc)
        l []
    else l
  in
  (* We interpret all declarations in the same evar_map, i.e. as a telescope. *)
  let (sigma,_,_),l = List.fold_left_map (fun (sigma,env,ienv) (is_coe,(idl,c)) ->
    let sigma,t,imps = interp_assumption ~program_mode env sigma ienv [] c in
    let r = Retyping.relevance_of_type env sigma t in
    let env =
      EConstr.push_named_context (List.map (fun {CAst.v=id} -> LocalAssum (make_annot id r,t)) idl) env in
    let ienv = List.fold_right (fun {CAst.v=id} ienv ->
      let impls = compute_internalization_data env sigma id Variable t imps in
      Id.Map.add id impls ienv) idl ienv in
      ((sigma,env,ienv),((is_coe,idl),t,imps)))
    (sigma,env,empty_internalization_env) l
  in
  let sigma = solve_remaining_evars all_and_fail_flags env sigma in
  (* The universe constraints come from the whole telescope. *)
  let sigma = Evd.minimize_universes sigma in
  let nf_evar c = EConstr.to_constr sigma c in
  let uvars, l = List.fold_left_map (fun uvars (coe,t,imps) ->
      let t = nf_evar t in
      let uvars = Univ.Level.Set.union uvars (Vars.universes_of_constr t) in
      uvars, (coe,t,imps))
      Univ.Level.Set.empty l
  in
  (* XXX: Using `Declare.prepare_parameter` here directly is not
     possible as we indeed declare several parameters; however,
     restrict_universe_context should be called in a centralized place
     IMO, thus I think we should adapt `prepare_parameter` to handle
     this case too. *)
  let sigma = Evd.restrict_universe_context sigma uvars in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  declare_assumptions ~poly ~scope ~kind univs nl l

let context_subst subst (name,b,t,impl) =
  name, Option.map (Vars.substl subst) b, Vars.substl subst t, impl

let context_insection sigma ~poly ctx =
  let uctx = Evd.evar_universe_context sigma in
  let univs = UState.univ_entry ~poly uctx in
  let fn i subst (name,_,_,_ as d) =
    let d = context_subst subst d in
    let univs = if i = 0 then univs else empty_univ_entry ~poly in
    let () = match d with
      | name, None, t, impl ->
        let kind = Decls.Context in
        declare_variable false ~kind t univs [] impl (CAst.make name)
      | name, Some b, t, impl ->
        let entry = Declare.definition_entry ~univs ~types:t b in
        (* XXX Fixme: Use Declare.prepare_definition *)
        let kind = Decls.(IsDefinition Definition) in
        let _ : GlobRef.t =
          Declare.declare_entry ~name ~scope:Locality.Discharge
            ~kind ~impargs:[] ~uctx entry
        in
        ()
    in
    Constr.mkVar name :: subst
  in
  let _ : Vars.substl = List.fold_left_i fn 0 [] ctx in
  ()

let context_nosection sigma ~poly ctx =
  let (univ_entry,ubinders as univs) = Evd.univ_entry ~poly sigma in
  let fn i subst d =
    let (name,b,t,_impl) = context_subst subst d in
    let kind = Decls.(IsAssumption Logical) in
    let local = if Lib.is_modtype () then Locality.ImportDefaultBehavior
      else Locality.ImportNeedQualified
    in
    (* Multiple monomorphic axioms: declare universes only on the first declaration *)
    let univs = if i = 0 then univs else clear_univs (Locality.Global local) univs in
    let decl = match b with
      | None ->
        let entry = Declare.parameter_entry ~univs:(univ_entry, ubinders) t in
        Declare.ParameterEntry entry
      | Some b ->
        let entry = Declare.definition_entry ~univs ~types:t b in
        Declare.DefinitionEntry entry
    in
    let cst = Declare.declare_constant ~name ~kind ~local decl in
    let () = Declare.assumption_message name in
    let env = Global.env () in
    (* why local when is_modtype? *)
    let locality = if Lib.is_modtype () then Hints.Local else Hints.SuperGlobal in
    let () = if Lib.is_modtype() || Option.is_empty b then
        Classes.declare_instance env sigma None locality (GlobRef.ConstRef cst)
    in
    Constr.mkConstU (cst,instance_of_univ_entry univ_entry) :: subst
  in
  let _ : Vars.substl = List.fold_left_i fn 0 [] ctx in
  ()

let interp_context env sigma l =
  let sigma, (_, ((_env, ctx), impls)) = interp_context_evars ~program_mode:false env sigma l in
  (* Note, we must use the normalized evar from now on! *)
  let ce t = Pretyping.check_evars env sigma t in
  let () = List.iter (fun decl -> Context.Rel.Declaration.iter_constr ce decl) ctx in
  let sigma, ctx = Evarutil.finalize
      sigma (fun nf -> List.map (RelDecl.map_constr_het nf) ctx) in
  (* reorder, evar-normalize and add implicit status *)
  let ctx = List.rev_map (fun d ->
      let {binder_name=name}, b, t = RelDecl.to_tuple d in
      let name = match name with
        | Anonymous -> user_err Pp.(str "Anonymous variables not allowed in contexts.")
        | Name id -> id
      in
      let impl = let open Glob_term in
      let search x = match x.CAst.v with
        | Some (Name id',max) when Id.equal name id' ->
          Some (if max then MaxImplicit else NonMaxImplicit)
        | _ -> None
        in
        try CList.find_map search impls with Not_found -> Explicit
      in
      name,b,t,impl)
      ctx
  in
   sigma, ctx

let do_context ~poly l =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let sigma, ctx = interp_context env sigma l in
  if Global.sections_are_opened ()
  then context_insection sigma ~poly ctx
  else context_nosection sigma ~poly ctx
