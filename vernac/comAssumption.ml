(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Vars
open Declare
open Names
open Context
open Globnames
open Constrexpr_ops
open Constrintern
open Impargs
open Decl_kinds
open Pretyping
open Entries

module RelDecl = Context.Rel.Declaration
(* 2| Variable/Hypothesis/Parameter/Axiom declarations *)

let axiom_into_instance = ref false

let () =
  let open Goptions in
  declare_bool_option
    { optdepr = true;
      optname = "automatically declare axioms whose type is a typeclass as instances";
      optkey = ["Typeclasses";"Axioms";"Are";"Instances"];
      optread = (fun _ -> !axiom_into_instance);
      optwrite = (:=) axiom_into_instance; }

let should_axiom_into_instance = function
  | Context ->
    (* The typeclass behaviour of Variable and Context doesn't depend
       on section status *)
    true
  | Definitional | Logical | Conjectural -> !axiom_into_instance

let declare_assumption is_coe ~poly ~scope ~kind typ univs pl imps impl nl {CAst.v=ident} =
let open DeclareDef in
match scope with
| Discharge ->
  let univs = match univs with
    | Monomorphic_entry univs -> univs
    | Polymorphic_entry (_, univs) -> Univ.ContextSet.of_context univs
  in
  let decl = (Lib.cwd(), SectionLocalAssum {typ;univs;poly;impl}, IsAssumption kind) in
  let _ = declare_variable ident decl in
  let () = assumption_message ident in
  let r = VarRef ident in
  let () = maybe_declare_manual_implicits true r imps in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let () = Classes.declare_instance env sigma None true r in
  let () = if is_coe then Class.try_add_new_coercion r ~local:true ~poly:false in
  (r,Univ.Instance.empty,true)

| Global local ->
  let do_instance = should_axiom_into_instance kind in
  let inl = let open Declaremods in match nl with
    | NoInline -> None
    | DefaultInline -> Some (Flags.get_inline_level())
    | InlineAt i -> Some i
  in
  let decl = (Declare.ParameterEntry (None,(typ,univs),inl), IsAssumption kind) in
  let kn = declare_constant ident ~local decl in
  let gr = ConstRef kn in
  let () = maybe_declare_manual_implicits false gr imps in
  let () = Declare.declare_univ_binders gr pl in
  let () = assumption_message ident in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let () = if do_instance then Classes.declare_instance env sigma None false gr in
  let local = match local with ImportNeedQualified -> true | ImportDefaultBehavior -> false in
  let () = if is_coe then Class.try_add_new_coercion gr ~local ~poly in
  let inst = match univs with
    | Polymorphic_entry (_, univs) -> Univ.UContext.instance univs
    | Monomorphic_entry _ -> Univ.Instance.empty
  in
    (gr,inst,Lib.is_modtype_strict ())

let interp_assumption ~program_mode sigma env impls c =
  let sigma, (ty, impls) = interp_type_evars_impls ~program_mode env sigma ~impls c in
  sigma, (ty, impls)

(* When monomorphic the universe constraints are declared with the first declaration only. *)
let next_uctx =
  let empty_uctx = Monomorphic_entry Univ.ContextSet.empty in
  function
  | Polymorphic_entry _ as uctx -> uctx
  | Monomorphic_entry _ -> empty_uctx

let declare_assumptions idl is_coe ~scope ~poly ~kind typ uctx pl imps nl =
  let refs, status, _ =
    List.fold_left (fun (refs,status,uctx) id ->
      let ref',u',status' =
        declare_assumption is_coe ~scope ~poly ~kind typ uctx pl imps false nl id in
      (ref',u')::refs, status' && status, next_uctx uctx)
      ([],true,uctx) idl
  in
  List.rev refs, status


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
  let uctx = Evd.check_univ_decl ~poly sigma udecl in
  let ubinders = Evd.universe_binders sigma in
  pi2 (List.fold_left (fun (subst,status,uctx) ((is_coe,idl),typ,imps) ->
      let typ = replace_vars subst typ in
      let refs, status' = declare_assumptions idl is_coe ~poly ~scope ~kind typ uctx ubinders imps nl in
      let subst' = List.map2
          (fun {CAst.v=id} (c,u) -> (id, Constr.mkRef (c,u)))
          idl refs
      in
      subst'@subst, status' && status, next_uctx uctx)
    ([], true, uctx) l)

let do_primitive id prim typopt =
  if Lib.sections_are_opened () then
    CErrors.user_err Pp.(str "Declaring a primitive is not allowed in sections.");
  if Dumpglob.dump () then Dumpglob.dump_definition id false "ax";
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, typopt = Option.fold_left_map
      (interp_type_evars_impls ~impls:empty_internalization_env env)
      evd typopt
  in
  let evd = Evd.minimize_universes evd in
  let uvars, impls, typopt = match typopt with
    | None -> Univ.LSet.empty, [], None
    | Some (ty,impls) ->
      EConstr.universes_of_constr evd ty, impls, Some (EConstr.to_constr evd ty)
  in
  let evd = Evd.restrict_universe_context evd uvars in
  let uctx = UState.check_mono_univ_decl (Evd.evar_universe_context evd) UState.default_univ_decl in
  let entry = { prim_entry_type = typopt;
                prim_entry_univs = uctx;
                prim_entry_content = prim;
              }
  in
  let _kn = declare_constant id.CAst.v (PrimitiveEntry entry,IsPrimitive) in
  Flags.if_verbose Feedback.msg_info Pp.(Id.print id.CAst.v ++ str " is declared")

let named_of_rel_context l =
  let open EConstr.Vars in
  let open RelDecl in
  let acc, ctx =
    List.fold_right
      (fun decl (subst, ctx) ->
         let id = match get_name decl with Anonymous -> invalid_arg "named_of_rel_context" | Name id -> id in
               let d = match decl with
           | LocalAssum (_,t) -> id, None, substl subst t
           | LocalDef (_,b,t) -> id, Some (substl subst b), substl subst t in
               (EConstr.mkVar id :: subst, d :: ctx))
      l ([], [])
  in ctx

let context ~poly l =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let sigma, (_, ((env', fullctx), impls)) = interp_context_evars ~program_mode:false env sigma l in
  (* Note, we must use the normalized evar from now on! *)
  let sigma = Evd.minimize_universes sigma in
  let ce t = Pretyping.check_evars env (Evd.from_env env) sigma t in
  let () = List.iter (fun decl -> Context.Rel.Declaration.iter_constr ce decl) fullctx in
  let ctx =
    try named_of_rel_context fullctx
    with e when CErrors.noncritical e ->
      user_err Pp.(str "Anonymous variables not allowed in contexts.")
  in
  let univs =
    match ctx with
    | [] -> assert false
    | [_] -> Evd.univ_entry ~poly sigma
    | _::_::_ ->
      if Lib.sections_are_opened ()
      then
        (* More than 1 variable in a section: we can't associate
           universes to any specific variable so we declare them
           separately. *)
        begin
          let uctx = Evd.universe_context_set sigma in
          Declare.declare_universe_context ~poly uctx;
          if poly then Polymorphic_entry ([||], Univ.UContext.empty)
          else Monomorphic_entry Univ.ContextSet.empty
        end
      else if poly then
        (* Multiple polymorphic axioms: they are all polymorphic the same way. *)
        Evd.univ_entry ~poly sigma
      else
        (* Multiple monomorphic axioms: declare universes separately
           to avoid redeclaring them. *)
        begin
          let uctx = Evd.universe_context_set sigma in
          Declare.declare_universe_context ~poly uctx;
          Monomorphic_entry Univ.ContextSet.empty
        end
  in
  let fn status (id, b, t) =
    let b, t = Option.map (EConstr.to_constr sigma) b, EConstr.to_constr sigma t in
    if Lib.is_modtype () && not (Lib.sections_are_opened ()) then
      (* Declare the universe context once *)
      let decl = match b with
      | None ->
        (Declare.ParameterEntry (None,(t,univs),None), IsAssumption Logical)
      | Some b ->
        let entry = Declare.definition_entry ~univs ~types:t b in
        (Declare.DefinitionEntry entry, IsAssumption Logical)
      in
      let cst = Declare.declare_constant id decl in
      let env = Global.env () in
      Classes.declare_instance env sigma (Some Hints.empty_hint_info) true (ConstRef cst);
      status
    else
      let test x = match x.CAst.v with
      | Some (Name id',_) -> Id.equal id id'
      | _ -> false
      in
      let impl = List.exists test impls in
      let scope =
        if Lib.sections_are_opened () then DeclareDef.Discharge else DeclareDef.Global ImportDefaultBehavior in
      let nstatus = match b with
      | None ->
        pi3 (declare_assumption false ~scope ~poly ~kind:Context t univs UnivNames.empty_binders [] impl
               Declaremods.NoInline (CAst.make id))
      | Some b ->
        let entry = Declare.definition_entry ~univs ~types:t b in
        let _gr = DeclareDef.declare_definition
            ~name:id ~scope:DeclareDef.Discharge
            ~kind:Definition UnivNames.empty_binders entry [] in
        Lib.sections_are_opened () || Lib.is_modtype_strict ()
      in
        status && nstatus
  in
  List.fold_left fn true (List.rev ctx)
