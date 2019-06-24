(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars

open Util
open Termops
open EConstr
open Decl_kinds
open Evarutil

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

let rec shrink ctx sign c t accu =
  let open Constr in
  let open CVars in
  match ctx, sign with
  | [], [] -> (c, t, accu)
  | p :: ctx, decl :: sign ->
      if noccurn 1 c && noccurn 1 t then
        let c = subst1 mkProp c in
        let t = subst1 mkProp t in
        shrink ctx sign c t accu
      else
        let c = Term.mkLambda_or_LetIn p c in
        let t = Term.mkProd_or_LetIn p t in
        let accu = if RelDecl.is_local_assum p
                   then mkVar (NamedDecl.get_id decl) :: accu
                   else accu
    in
    shrink ctx sign c t accu
| _ -> assert false

let shrink_entry sign const =
  let open Proof_global in
  let typ = match const.proof_entry_type with
  | None -> assert false
  | Some t -> t
  in
  (* The body has been forced by the call to [build_constant_by_tactic] *)
  let () = assert (Future.is_over const.proof_entry_body) in
  let ((body, uctx), eff) = Future.force const.proof_entry_body in
  let (body, typ, ctx) = decompose (List.length sign) body typ [] in
  let (body, typ, args) = shrink ctx sign body typ [] in
  let const = { const with
    proof_entry_body = Future.from_val ((body, uctx), eff);
    proof_entry_type = Some typ;
  } in
  (const, args)

let name_op_to_name ~name_op ~name suffix =
  match name_op with
  | Some s -> s
  | None -> Nameops.add_suffix name suffix

let cache_term_by_tactic_then ~opaque ~name_op ?(goal_type=None) tac tacK =
  let open Tacticals.New in
  let open Tacmach.New in
  let open Proofview.Notations in
  Proofview.tclProofInfo [@ocaml.warning "-3"] >>= fun (name, poly) ->
  (* This is important: The [Global] and [Proof Theorem] parts of the
     goal_kind are not relevant here as build_constant_by_tactic does
     use the noop terminator; but beware if some day we remove the
     redundancy on constant declaration. This opens up an interesting
     question, how does abstract behave when discharge is local for example?
  *)
  let suffix = if opaque
    then "_subproof"
    else "_subterm" in
  let name = name_op_to_name ~name_op ~name suffix in
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
  let name = Namegen.next_global_ident_away name (pf_ids_set_of_hyps gl) in
  let concl = match goal_type with
              | None ->  Proofview.Goal.concl gl
              | Some ty -> ty in
  let concl = it_mkNamedProd_or_LetIn concl sign in
  let concl =
    try flush_and_check_evars !evdref concl
    with Uninstantiated_evar _ ->
      CErrors.user_err Pp.(str "\"abstract\" cannot handle existentials.") in

  let evd, ctx, concl =
    (* FIXME: should be done only if the tactic succeeds *)
    let evd = Evd.minimize_universes !evdref in
    let ctx = Evd.universe_context_set evd in
      evd, ctx, Evarutil.nf_evars_universes evd concl
  in
  let concl = EConstr.of_constr concl in
  let solve_tac = tclCOMPLETE (tclTHEN (tclDO (List.length sign) Tactics.intro) tac) in
  let ectx = Evd.evar_universe_context evd in
  let (const, safe, ectx) =
    try Pfedit.build_constant_by_tactic ~poly ~name ectx secsign concl solve_tac
    with Logic_monad.TacticFailure e as src ->
    (* if the tactic [tac] fails, it reports a [TacticFailure e],
       which is an error irrelevant to the proof system (in fact it
       means that [e] comes from [tac] failing to yield enough
       success). Hence it reraises [e]. *)
    let (_, info) = CErrors.push src in
    iraise (e, info)
  in
  let const, args = shrink_entry sign const in
  let args = List.map EConstr.of_constr args in
  let cd = Declare.DefinitionEntry { const with Proof_global.proof_entry_opaque = opaque } in
  let decl = (cd, if opaque then IsProof Lemma else IsDefinition Definition) in
  let cst () =
    (* do not compute the implicit arguments, it may be costly *)
    let () = Impargs.make_implicit_args false in
    (* ppedrot: seems legit to have abstracted subproofs as local*)
    Declare.declare_private_constant ~local:Declare.ImportNeedQualified name decl
  in
  let cst, eff = Impargs.with_implicit_protection cst () in
  let inst = match const.Proof_global.proof_entry_universes with
  | Entries.Monomorphic_entry _ -> EInstance.empty
  | Entries.Polymorphic_entry (_, ctx) ->
    (* We mimic what the kernel does, that is ensuring that no additional
       constraints appear in the body of polymorphic constants. Ideally this
       should be enforced statically. *)
    let (_, body_uctx), _ = Future.force const.Proof_global.proof_entry_body in
    let () = assert (Univ.ContextSet.is_empty body_uctx) in
    EInstance.make (Univ.UContext.instance ctx)
  in
  let lem = mkConstU (cst, inst) in
  let evd = Evd.set_universe_context evd ectx in
  let effs = Evd.concat_side_effects eff
    Proof_global.(snd (Future.force const.proof_entry_body)) in
  let solve =
    Proofview.tclEFFECTS effs <*>
    tacK lem args
  in
  let tac = if not safe then Proofview.mark_as_unsafe <*> solve else solve in
  Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evd) tac
  end

let abstract_subproof ~opaque tac =
  cache_term_by_tactic_then ~opaque tac (fun lem args -> Tactics.exact_no_check (applist (lem, args)))

let tclABSTRACT ?(opaque=true) name_op tac =
  abstract_subproof ~opaque ~name_op tac
