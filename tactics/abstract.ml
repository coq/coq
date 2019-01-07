(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars

open Util
open Names
open Termops
open EConstr
open Decl_kinds

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(* tactical to save as name a subproof such that the generalisation of
   the current goal, abstracted with respect to the local signature,
   is solved by tac *)

(** d1 is the section variable in the global context, d2 in the goal context *)
let interpretable_as_section_decl env evd d1 d2 =
  let open Context.Named.Declaration in
  let e_eq_constr_univs sigma c1 c2 = match eq_constr_universes env !sigma c1 c2 with
  | None -> false
  | Some cstr ->
    try ignore (Evd.add_universe_constraints !sigma cstr); true
    with UState.UniversesDiffer -> false
  in
  match d2, d1 with
  | LocalDef _, LocalAssum _ -> false
  | LocalDef (_,b1,t1), LocalDef (_,b2,t2) ->
    e_eq_constr_univs evd b1 b2 && e_eq_constr_univs evd t1 t2
  | LocalAssum (_,t1), d2 -> e_eq_constr_univs evd t1 (NamedDecl.get_type d2)

let rec decompose len c t accu =
  let open Constr in
  let open Context.Rel.Declaration in
  if len = 0 then (c, t, accu)
  else match kind c, kind t with
  | Lambda (na, u, c), Prod (_, _, t) ->
    decompose (pred len) c t (LocalAssum (na, u) :: accu)
  | LetIn (na, b, u, c), LetIn (_, _, _, t) ->
    decompose (pred len) c t (LocalDef (na, b, u) :: accu)
  | _ -> assert false

let rec shrink ctx sign c t targs accu =
  let open Constr in
  let open CVars in
  match ctx, sign with
  | [], [] -> (c, t, accu, targs)
  | p :: ctx, decl :: sign ->
      if noccurn 1 c && noccurn 1 t then
        let c = subst1 mkProp c in
        let t = subst1 mkProp t in
        let targs = subst1 mkProp targs in
        shrink ctx sign c t targs accu
      else
        let c = Term.mkLambda_or_LetIn p c in
        let t = Term.mkProd_or_LetIn p t in
        let accu, targs =
          let v = mkVar (NamedDecl.get_id decl) in
          (if RelDecl.is_local_assum p then v :: accu else accu),
          subst1 v targs
        in
        shrink ctx sign c t targs accu
| _ -> assert false

let shrink_entry sign const =
  let open Entries in
  let typ = match const.const_entry_type with
  | None -> assert false
  | Some t -> t
  in
  (* The body has been forced by the call to [build_constant_by_tactic] *)
  let () = assert (Future.is_over const.const_entry_body) in
  let ((body, uctx), eff) = Future.force const.const_entry_body in
  let (body, typ, ctx) = decompose (List.length sign) body typ [] in
  let (body, typ, args, ty_bodyargs) = shrink ctx sign body typ typ [] in
  let const = { const with
    const_entry_body = Future.from_val ((body, uctx), eff);
    const_entry_type = Some typ;
  } in
  (const, args, ty_bodyargs)

let cache_term_by_tactic_then ~opaque ?(goal_type=None) id gk tac tacK =
  let open Tacticals.New in
  let open Tacmach.New in
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let current_sign = Global.named_context_val ()
  and global_sign = Proofview.Goal.hyps gl in
  let evdref = ref sigma in
  let sign,secsign =
    List.fold_right
      (fun d (s1,s2) ->
        let id = NamedDecl.get_id d in
        if mem_named_context_val id current_sign &&
          interpretable_as_section_decl env evdref (lookup_named_val id current_sign) d
        then (s1,push_named_context_val d s2)
        else (Context.Named.add d s1,s2))
      global_sign (Context.Named.empty, Environ.empty_named_context_val) in
  let id = Namegen.next_global_ident_away id (pf_ids_set_of_hyps gl) in
  let orig_concl = match goal_type with
              | None ->  Proofview.Goal.concl gl
              | Some ty -> ty in
  let concl = it_mkNamedProd_or_LetIn orig_concl sign in

  let sigma_concl =
    Evarutil.shrink !evdref (Evarutil.undefined_evars_of_term !evdref concl) in

  let evd, ctx, concl =
    (* FIXME: should be done only if the tactic succeeds *)
    let evd = Evd.minimize_universes !evdref in
    let ctx = Evd.universe_context_set evd in
      evd, ctx, Evarutil.nf_evars_universes evd (EConstr.to_constr ~abort_on_undefined_evars:false !evdref concl)
  in
  let concl = EConstr.of_constr concl in
  let solve_tac = tclCOMPLETE (tclTHEN (tclDO (List.length sign) Tactics.intro) tac) in
  let (const, safe, ectx) =
    try Pfedit.build_constant_by_tactic ~goal_kind:gk id sigma_concl secsign concl solve_tac
    with Logic_monad.TacticFailure e as src ->
    (* if the tactic [tac] fails, it reports a [TacticFailure e],
       which is an error irrelevant to the proof system (in fact it
       means that [e] comes from [tac] failing to yield enough
       success). Hence it reraises [e]. *)
    let (_, info) = CErrors.push src in
    iraise (e, info)
  in
  let const, args, const_args_typ = shrink_entry sign const in
  let args = List.map EConstr.of_constr args in
  let const_args_typ = EConstr.of_constr const_args_typ in
  let cd = Entries.DefinitionEntry { const with Entries.const_entry_opaque = opaque } in
  let decl = (cd, if opaque then IsProof Lemma else IsDefinition Definition) in
  let cst () =
    (* do not compute the implicit arguments, it may be costly *)
    let () = Impargs.make_implicit_args false in
    (* ppedrot: seems legit to have abstracted subproofs as local*)
    Declare.declare_constant ~internal:Declare.InternalTacticRequest ~local:true id decl
  in
  let cst = Impargs.with_implicit_protection cst () in
  let inst = match const.Entries.const_entry_universes with
  | Entries.Monomorphic_const_entry _ -> EInstance.empty
  | Entries.Polymorphic_const_entry (_, ctx) ->
    (* We mimick what the kernel does, that is ensuring that no additional
       constraints appear in the body of polymorphic constants. Ideally this
       should be enforced statically. *)
    let (_, body_uctx), _ = Future.force const.Entries.const_entry_body in
    let () = assert (Univ.ContextSet.is_empty body_uctx) in
    EInstance.make (Univ.UContext.instance ctx)
  in
  let lem = mkConstU (cst, inst) in
  let evd = Evd.set_universe_context evd ectx in
  let open Safe_typing in
  let eff = private_con_of_con (Global.safe_env ()) cst in
  let effs = concat_private eff
    Entries.(snd (Future.force const.const_entry_body)) in
  let unify = Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    match Evarconv.cumul env sigma const_args_typ orig_concl with
    | Some sigma -> Proofview.Unsafe.tclEVARS sigma
    | None ->
      Pretype_errors.error_actual_type_core env sigma
        { Environ.uj_val = applist (lem, args); uj_type = const_args_typ } orig_concl
    end in
  let solve =
    Proofview.tclEFFECTS effs <*> unify <*> tacK lem args in
  let tac = if not safe then Proofview.mark_as_unsafe <*> solve else solve in
  Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evd) tac
  end

let abstract_subproof ~opaque id gk tac =
  cache_term_by_tactic_then ~opaque id gk tac (fun lem args ->
    Tactics.exact_no_check (applist (lem, args)))

let anon_id = Id.of_string "anonymous"

let name_op_to_name name_op object_kind suffix =
  let open Proof_global in
  let default_gk = (Global, false, object_kind) in
  let name, gk = match Proof_global.V82.get_current_initial_conclusions () with
  | (id, (_, gk)) -> Some id, gk
  | exception NoCurrentProof -> None, default_gk
  in
  match name_op with
  | Some s -> s, gk
  | None ->
    let name = Option.default anon_id name in
    Nameops.add_suffix name suffix, gk

let tclABSTRACT ?(opaque=true) name_op tac =
  let s, gk = if opaque
    then name_op_to_name name_op (Proof Theorem) "_subproof"
    else name_op_to_name name_op (DefinitionBody Definition) "_subterm" in
  abstract_subproof ~opaque s gk tac
