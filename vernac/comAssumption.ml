(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Context
open Constrintern
open Impargs
open Pretyping

module NamedDecl = Context.Named.Declaration

(* 2| Variable/Hypothesis/Parameter/Axiom declarations *)

(** Declares a local variable/let, possibly declaring it:
    - as a coercion (is_coe)
    - as a type class instance
    - with implicit arguments (impls)
    - with implicit status for discharge (impl)
    - virtually with named universes *)
let declare_local ~coe ~try_assum_as_instance ~kind ~univs ~impargs ~impl ~name body typ =
  let decl = match body with
    | None ->
      Declare.SectionLocalAssum {typ; impl; univs}
    | Some b ->
      Declare.SectionLocalDef {clearbody = (* TODO *) false; entry = Declare.definition_entry ~univs ~types:typ b} in
  let () = Declare.declare_variable ~name ~kind ~typing_flags:None decl in
  let () = if body = None then Declare.assumption_message name else Declare.definition_message name in
  let r = GlobRef.VarRef name in
  let () = maybe_declare_manual_implicits true r impargs in
  let _ = if try_assum_as_instance && Option.is_empty body then
      let env = Global.env () in
      let sigma = Evd.from_env env in
      Classes.declare_instance env sigma None Hints.Local r in
  let () =
    if coe = Vernacexpr.AddCoercion then
      ComCoercion.try_add_new_coercion
        r ~local:true ~reversible:false in
  (r, UVars.Instance.empty)

let declare_variable ~coe ~kind ~univs ~impargs ~impl ~name typ =
  declare_local ~coe ~try_assum_as_instance:true ~kind:(Decls.IsAssumption kind) ~univs ~impargs ~impl ~name None typ

let instance_of_univ_entry = function
  | UState.Polymorphic_entry univs -> UVars.UContext.instance univs
  | UState.Monomorphic_entry _ -> UVars.Instance.empty

(** Declares a global axiom/parameter, possibly declaring it:
    - as a coercion
    - as a type class instance
    - with implicit arguments
    - with inlining for functor application
    - with named universes *)
let declare_global ~coe ~try_assum_as_instance ~local ~kind ?user_warns ~univs ~impargs ~inline ~name body typ =
  let (uentry, ubinders) = univs in
  let inl = let open Declaremods in match inline with
    | NoInline -> None
    | DefaultInline -> Some (Flags.get_inline_level())
    | InlineAt i -> Some i
  in
  let decl = match body with
    | None -> Declare.ParameterEntry (Declare.parameter_entry ~univs:(uentry, ubinders) ?inline:inl typ)
    | Some b -> Declare.DefinitionEntry (Declare.definition_entry ~univs ~types:typ b) in
  let kn = Declare.declare_constant ~name ~local ~kind ?user_warns decl in
  let gr = GlobRef.ConstRef kn in
  let () = maybe_declare_manual_implicits false gr impargs in
  let () = match body with None -> Declare.assumption_message name | Some _ -> Declare.definition_message name in
  let local = match local with
    | Locality.ImportNeedQualified -> true
    | Locality.ImportDefaultBehavior -> false
  in
  let () = if try_assum_as_instance && Option.is_empty body then
      (* why local when is_modtype? *)
      let env = Global.env () in
      let sigma = Evd.from_env env in
      Classes.declare_instance env sigma None Hints.SuperGlobal gr in
  let () =
    if coe = Vernacexpr.AddCoercion then
      ComCoercion.try_add_new_coercion
        gr ~local ~reversible:false in
  let inst = instance_of_univ_entry uentry in
  (gr,inst)

let declare_axiom ~coe ~local ~kind ?user_warns ~univs ~impargs ~inline ~name typ =
  declare_global ~coe ~try_assum_as_instance:false ~local ~kind:(Decls.IsAssumption kind) ?user_warns ~univs ~impargs ~inline ~name None typ

let interp_assumption ~program_mode env sigma impl_env bl c =
  let flags = { Pretyping.all_no_fail_flags with program_mode } in
  let sigma, (impls, ((env_bl, ctx), impls1)) = interp_context_evars ~program_mode ~impl_env env sigma bl in
  let sigma, (ty, impls2) = interp_type_evars_impls ~flags env_bl sigma ~impls c in
  let ty = EConstr.it_mkProd_or_LetIn ty ctx in
  sigma, ty, impls1@impls2

let empty_poly_univ_entry = UState.Polymorphic_entry UVars.UContext.empty, UnivNames.empty_binders
let empty_mono_univ_entry = UState.Monomorphic_entry Univ.ContextSet.empty, UnivNames.empty_binders
let empty_univ_entry poly = if poly then empty_poly_univ_entry else empty_mono_univ_entry

let clear_univs scope univ =
  match scope, univ with
  | Locality.Global _, (UState.Polymorphic_entry _, _ as univs) -> univs
  | _, (UState.Monomorphic_entry _, _) -> empty_univ_entry false
  | Locality.Discharge, (UState.Polymorphic_entry _, _) -> empty_univ_entry true

let context_subst subst (id,b,t,infos) =
  id, Option.map (Vars.replace_vars subst) b, Vars.replace_vars subst t, infos

let declare_context ~try_global_assum_as_instance ~scope ~univs ?user_warns ~inline ctx =
  let fn i subst d =
    let (name,b,t,(impl,kind,coe,impargs)) = context_subst subst d in
    let univs = if i = 0 then univs else clear_univs scope univs in
    let refu = match scope with
      | Locality.Discharge -> declare_local ~coe ~try_assum_as_instance:true ~kind ~univs ~impargs ~impl ~name b t
      | Locality.Global local -> declare_global ~coe ~try_assum_as_instance:try_global_assum_as_instance ~local ~kind ?user_warns ~univs ~impargs ~inline ~name b t in
    (name, Constr.mkRef refu) :: subst
  in
  let _ = List.fold_left_i fn 0 [] ctx in
  ()

let error_extra_universe_decl ?loc () =
  user_err ?loc
      Pp.(strbrk "When declaring multiple assumptions in one command, " ++
          strbrk "only the first name is allowed to mention a universe binder " ++
          strbrk "(which will be shared by the whole block).")

let extract_assumption_names = function
  | ({CAst.loc;v=id}, Some _) -> error_extra_universe_decl ?loc ()
  | (id, None) -> id

let process_assumptions_udecls = function
  | (coe, ((id, udecl)::ids, c))::assums ->
    let ids = List.map extract_assumption_names ids in
    let assums = List.map (fun (coe, (idl, c)) -> (coe, (List.map extract_assumption_names idl, c))) assums in
    udecl, (coe,(id::ids,c))::assums
  | (_, ([], _))::_ | [] -> assert false

let error_polymorphic_section_variable ?loc () =
  user_err ?loc (Pp.str "Section variables cannot be polymorphic.")

let process_assumptions_no_udecls l =
  List.map (fun (coe, (ids, c)) ->
      (coe, (List.map (function
                 | ({CAst.loc}, Some _) -> error_polymorphic_section_variable ?loc ()
                 | (id, None) -> id) ids, c))) l

let extract_manual_implicit e =
  CAst.make (match e with
    | Some {impl_pos = (na,_,_); impl_expl = Manual; impl_max = max} -> Some (na,max)
    | Some {impl_expl = (DepFlexAndRigid _ | DepFlex _ | DepRigid _ )} | None -> None)

let find_implicits id ienv =
  try
    let impls = implicits_of_decl_in_internalization_env id ienv in
    List.map extract_manual_implicit impls
  with Not_found -> []

let local_binders_of_decls ~poly l =
  let coercions, l =
    List.fold_left_map (fun coercions (is_coe,(idl,c)) ->
      let coercions = match is_coe with
        | Vernacexpr.NoCoercion -> coercions
        | Vernacexpr.AddCoercion -> List.fold_right (fun id -> Id.Set.add id.CAst.v) idl coercions in
      let make_name id = CAst.make ?loc:id.CAst.loc (Name id.CAst.v) in
      let make_assum idl = Constrexpr.(CLocalAssum (List.map make_name idl,None,Default Glob_term.Explicit,c)) in
      let decl = if poly then
        (* Separate declarations so that A B : Type puts A and B in different levels. *)
        List.map (fun id -> make_assum [id]) idl
      else
        [make_assum idl] in
      (coercions,decl)) Id.Set.empty l in
  coercions, List.flatten l

let find_binding_kind id impls =
  let open Glob_term in
  let find x = match x.CAst.v with
    | Some (Name id',max) when Id.equal id id' -> Some (if max then MaxImplicit else NonMaxImplicit)
    | _ -> None in
  Option.default Explicit (CList.find_map find impls)

let interp_context_gen ~program_mode ~kind ~autoimp_enable ~coercions env sigma l =
  let initial = sigma in
  let sigma, (ienv, ((env, ctx), impls)) = interp_named_context_evars ~program_mode ~autoimp_enable env sigma l in
  (* Note, we must use the normalized evar from now on! *)
  let sigma = solve_remaining_evars all_and_fail_flags env ~initial sigma in
  let sigma, ctx = Evarutil.finalize sigma @@ fun nf ->
    List.map (NamedDecl.map_constr_het (fun x -> x) nf) ctx
  in
  (* reorder, evar-normalize and add implicit status *)
  let ctx = List.rev_map (fun d ->
      let {binder_name=id}, b, t = NamedDecl.to_tuple d in
      let impl = find_binding_kind id impls in
      let kind = Decls.(if b = None then IsAssumption kind else IsDefinition (match kind with Context -> LetContext | _ -> Let)) in
      let is_coe = if Id.Set.mem id coercions then Vernacexpr.AddCoercion else Vernacexpr.NoCoercion in
      let impls = if autoimp_enable then find_implicits id ienv else [] in
      let data = (impl,kind,is_coe,impls) in
      (id,b,t,data))
      ctx
  in
   sigma, ctx

let do_assumptions ~program_mode ~poly ~scope ~kind ?user_warns ~inline l =
  let sec = Lib.sections_are_opened () in
  if Dumpglob.dump () then begin
    List.iter (fun (_,(idl,_)) ->
      List.iter (fun (lid, _) ->
          let ty = if sec then "var" else "ax" in
          Dumpglob.dump_definition lid sec ty) idl) l end;
  let env = Global.env () in
  let udecl, l = match scope with
    | Locality.Global import_behavior -> process_assumptions_udecls l
    | Locality.Discharge -> None, process_assumptions_no_udecls l in
  let sigma, udecl = interp_univ_decl_opt env udecl in
  let coercions, ctx = local_binders_of_decls ~poly l in
  let sigma, ctx = interp_context_gen ~program_mode ~kind ~autoimp_enable:true ~coercions env sigma ctx in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  declare_context ~try_global_assum_as_instance:false ~scope ~univs ?user_warns ~inline ctx

let warn_context_outside_section =
  CWarnings.create ~name:"context-outside-section"
    ~category:CWarnings.CoreCategories.vernacular
    ~default:CWarnings.AsError
    Pp.(fun () -> strbrk "Use of \"Context\" outside sections behaves \
                          as \"#[local] Parameter\" or \"#[local] \
                          Axiom\" followed by \"Existing Instance\" \
                          for typeclasses.")

let do_context ~program_mode ~poly ctx =
  let sec = Lib.sections_are_opened () in
  if not sec then warn_context_outside_section ();
  if Dumpglob.dump () then begin
    let l = List.map (function
        | Constrexpr.CLocalAssum (l, _, _, _) ->
           let ty = if sec then "var "else "ax" in List.map (fun n -> ty, n) l
        | Constrexpr.CLocalDef (n, _, _, _) ->
           let ty = if sec then "var "else "def" in [ty, n]
        | Constrexpr.CLocalPattern _ -> [])
      ctx in
    List.iter (function
        | ty, {CAst.v = Names.Name.Anonymous; _} -> ()
        | ty, {CAst.v = Names.Name.Name id; loc} ->
           Dumpglob.dump_definition (CAst.make ?loc id) sec ty)
      (List.flatten l) end;
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let scope =
    let open Locality in
    if sec then Discharge
    else Global (if Lib.is_modtype () then ImportDefaultBehavior else ImportNeedQualified)
  in
  let sigma, ctx = interp_context_gen ~program_mode ~kind:Context ~autoimp_enable:false ~coercions:Id.Set.empty env sigma ctx in
  let univs = Evd.univ_entry ~poly sigma in
  declare_context ~try_global_assum_as_instance:true ~scope ~univs ~inline:Declaremods.NoInline ctx

(* API compatibility (used in Elpi) *)

let interp_context env sigma ctx =
  let reverse_rel_context_of_reverse_named_context ctx =
    List.rev (snd (List.fold_left_i (fun n (subst, ctx) (id,b,t,impl) ->
        let decl = (id, Option.map (Vars.subst_vars subst) b, Vars.subst_vars subst t, impl) in
        (id :: subst, decl :: ctx)) 1 ([],[]) ctx)) in
  let sigma, ctx = interp_context_gen ~program_mode:false ~kind:Context ~autoimp_enable:false ~coercions:Id.Set.empty env sigma ctx in
  let ctx = List.map (fun (id,b,t,(impl,_,_,_)) -> (id,b,t,impl)) ctx in
  sigma, reverse_rel_context_of_reverse_named_context ctx
