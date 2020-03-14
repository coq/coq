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
open Constrexpr_ops
open Constrintern
open Impargs
open Pretyping
open Entries

module RelDecl = Context.Rel.Declaration
(* 2| Variable/Hypothesis/Parameter/Axiom declarations *)

let declare_variable is_coe ~kind typ imps impl {CAst.v=name} =
  let kind = Decls.IsAssumption kind in
  let decl = Declare.SectionLocalAssum {typ; impl} in
  let () = Declare.declare_variable ~name ~kind decl in
  let () = Declare.assumption_message name in
  let r = GlobRef.VarRef name in
  let () = maybe_declare_manual_implicits true r imps in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let () = Classes.declare_instance env sigma None true r in
  let () = if is_coe then ComCoercion.try_add_new_coercion r ~local:true ~poly:false in
  ()

let instance_of_univ_entry = function
  | Polymorphic_entry (_, univs) -> Univ.UContext.instance univs
  | Monomorphic_entry _ -> Univ.Instance.empty

let declare_axiom is_coe ~poly ~local ~kind typ (univs, pl) imps nl {CAst.v=name} =
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
  let decl = Declare.ParameterEntry (None,(typ,univs),inl) in
  let kn = Declare.declare_constant ~name ~local ~kind decl in
  let gr = GlobRef.ConstRef kn in
  let () = maybe_declare_manual_implicits false gr imps in
  let () = DeclareUniv.declare_univ_binders gr pl in
  let () = Declare.assumption_message name in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let () = if do_instance then Classes.declare_instance env sigma None false gr in
  let local = match local with
    | Declare.ImportNeedQualified -> true
    | Declare.ImportDefaultBehavior -> false
  in
  let () = if is_coe then ComCoercion.try_add_new_coercion gr ~local ~poly in
  let inst = instance_of_univ_entry univs in
  (gr,inst)

let interp_assumption ~program_mode sigma env impls c =
  let sigma, (ty, impls) = interp_type_evars_impls ~program_mode env sigma ~impls c in
  sigma, (ty, impls)

(* When monomorphic the universe constraints and universe names are
   declared with the first declaration only. *)
let next_univs =
  let empty_univs = Monomorphic_entry Univ.ContextSet.empty, UnivNames.empty_binders in
  function
  | Polymorphic_entry _, _ as univs -> univs
  | Monomorphic_entry _, _ -> empty_univs

let context_set_of_entry = function
  | Polymorphic_entry (_,uctx) -> Univ.ContextSet.of_context uctx
  | Monomorphic_entry uctx -> uctx

let declare_assumptions ~poly ~scope ~kind univs nl l =
  let open DeclareDef in
  let () = match scope with
    | Discharge ->
      (* declare universes separately for variables *)
      Declare.declare_universe_context ~poly (context_set_of_entry (fst univs))
    | Global _ -> ()
  in
  let _, _ = List.fold_left (fun (subst,univs) ((is_coe,idl),typ,imps) ->
      (* NB: here univs are ignored when scope=Discharge *)
      let typ = replace_vars subst typ in
      let univs,subst' =
        List.fold_left_map (fun univs id ->
            let refu = match scope with
              | Discharge ->
                declare_variable is_coe ~kind typ imps Glob_term.Explicit id;
                GlobRef.VarRef id.CAst.v, Univ.Instance.empty
              | Global local ->
                declare_axiom is_coe ~local ~poly ~kind typ univs imps nl id
            in
            next_univs univs, (id.CAst.v, Constr.mkRef refu))
          univs idl
      in
      subst'@subst, next_univs univs)
      ([], univs) l
  in
  ()

let maybe_error_many_udecls = function
  | ({CAst.loc;v=id}, Some _) ->
    user_err ?loc ~hdr:"many_universe_declarations"
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
  let open DeclareDef in
  let () = match scope, udecl with
    | Discharge, Some _ ->
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
    let sigma,(t,imps) = interp_assumption ~program_mode sigma env ienv c in
    let r = Retyping.relevance_of_type env sigma t in
    let env =
      EConstr.push_named_context (List.map (fun {CAst.v=id} -> LocalAssum (make_annot id r,t)) idl) env in
    let ienv = List.fold_right (fun {CAst.v=id} ienv ->
      let impls = compute_internalization_data env sigma Variable t imps in
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
      let uvars = Univ.LSet.union uvars (Vars.universes_of_constr t) in
      uvars, (coe,t,imps))
      Univ.LSet.empty l
  in
  (* XXX: Using `DeclareDef.prepare_parameter` here directly is not
     possible as we indeed declare several parameters; however,
     restrict_universe_context should be called in a centralized place
     IMO, thus I think we should adapt `prepare_parameter` to handle
     this case too. *)
  let sigma = Evd.restrict_universe_context sigma uvars in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  let ubinders = Evd.universe_binders sigma in
  declare_assumptions ~poly ~scope ~kind (univs,ubinders) nl l

let context_subst subst (name,b,t,impl) =
  name, Option.map (Vars.substl subst) b, Vars.substl subst t, impl

let context_insection sigma ~poly ctx =
  let uctx = Evd.universe_context_set sigma in
  let () = Declare.declare_universe_context ~poly uctx in
  let fn subst (name,_,_,_ as d) =
    let d = context_subst subst d in
    let () = match d with
      | name, None, t, impl ->
        let kind = Decls.Context in
        declare_variable false ~kind t [] impl (CAst.make name)
      | name, Some b, t, impl ->
        (* We need to get poly right for check_same_poly *)
        let univs = if poly then Polymorphic_entry ([| |], Univ.UContext.empty)
          else Monomorphic_entry Univ.ContextSet.empty
        in
        let entry = Declare.definition_entry ~univs ~types:t b in
        (* XXX Fixme: Use DeclareDef.prepare_definition *)
        let entry = DeclareDef.ClosedDef.of_proof_entry entry in
        let _ : GlobRef.t = DeclareDef.declare_definition ~name ~scope:DeclareDef.Discharge
            ~kind:Decls.(IsDefinition Definition) ~ubind:UnivNames.empty_binders ~impargs:[] entry
        in
        ()
    in
    Constr.mkVar name :: subst
  in
  let _ : Vars.substl = List.fold_left fn [] ctx in
  ()

let context_nosection sigma ~poly ctx =
  let univs =
    match ctx, poly with
    | [_], _ | _, true -> Evd.univ_entry ~poly sigma
    | _, false ->
      (* Multiple monomorphic axioms: declare universes separately to
         avoid redeclaring them. *)
      let uctx = Evd.universe_context_set sigma in
      let () = Declare.declare_universe_context ~poly uctx in
      Monomorphic_entry Univ.ContextSet.empty
  in
  let fn subst d =
    let (name,b,t,_impl) = context_subst subst d in
    let kind = Decls.(IsAssumption Logical) in
    let decl = match b with
      | None ->
        Declare.ParameterEntry (None,(t,univs),None)
      | Some b ->
        let entry = Declare.definition_entry ~univs ~types:t b in
        Declare.DefinitionEntry entry
    in
    let local = if Lib.is_modtype () then Declare.ImportDefaultBehavior
      else Declare.ImportNeedQualified
    in
    let cst = Declare.declare_constant ~name ~kind ~local decl in
    let () = Declare.assumption_message name in
    let env = Global.env () in
    (* why local when is_modtype? *)
    let () = if Lib.is_modtype() || Option.is_empty b then
        Classes.declare_instance env sigma None (Lib.is_modtype()) (GlobRef.ConstRef cst)
    in
    Constr.mkConstU (cst,instance_of_univ_entry univs) :: subst
  in
  let _ : Vars.substl = List.fold_left fn [] ctx in
  ()

let context ~poly l =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let sigma, (_, ((_env, ctx), impls)) = interp_context_evars ~program_mode:false env sigma l in
  (* Note, we must use the normalized evar from now on! *)
  let sigma = Evd.minimize_universes sigma in
  let ce t = Pretyping.check_evars env sigma t in
  let () = List.iter (fun decl -> Context.Rel.Declaration.iter_constr ce decl) ctx in
  (* reorder, evar-normalize and add implicit status *)
  let ctx = List.rev_map (fun d ->
      let {binder_name=name}, b, t = RelDecl.to_tuple d in
      let name = match name with
        | Anonymous -> user_err Pp.(str "Anonymous variables not allowed in contexts.")
        | Name id -> id
      in
      let b = Option.map (EConstr.to_constr sigma) b in
      let t = EConstr.to_constr sigma t in
      let test x = match x.CAst.v with
        | Some (Name id',_) -> Id.equal name id'
        | _ -> false
      in
      let impl = Glob_term.(if List.exists test impls then MaxImplicit else Explicit) in (* ??? *)
      name,b,t,impl)
      ctx
  in
  if Global.sections_are_opened ()
  then context_insection sigma ~poly ctx
  else context_nosection sigma ~poly ctx
