(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

module NamedDecl = Context.Named.Declaration

(**********************************************************************)
(* Shortcut to build a term using tactics *)

let refine_by_tactic ~name ~poly ?(inline = false) env sigma ty tac =
  (* Save the initial side-effects to restore them afterwards. *)
  let eff = Evd.eval_side_effects sigma in
  let old_len = Safe_typing.length_private @@ Evd.seff_private eff in
  (* Save the existing goals *)
  let sigma = Evd.push_future_goals sigma in
  (* Start a proof *)
  let prf = Proof.start ~name ~poly sigma [env, ty] in
  let (prf, _, ()) =
    try Proof.run_tactic env tac prf
    with Logic_monad.TacticFailure e as src ->
      (* Catch the inner error of the monad tactic *)
      let (_, info) = Exninfo.capture src in
      Exninfo.iraise (e, info)
  in
  (* Plug back the retrieved sigma *)
  let Proof.{ goals; stack; sigma; entry } = Proof.data prf in
  let () = assert (stack = []) in
  let ans = match Proofview.initial_goals entry with
  | [_, c, _] -> c
  | _ -> assert false
  in
  let ans = EConstr.to_constr ~abort_on_undefined_evars:false sigma ans in
  let sigma, ans =
    if inline then
      (* [neff] contains the freshly generated side-effects *)
      let neff = Evd.seff_private @@ Evd.eval_side_effects sigma in
      let new_len = Safe_typing.length_private neff in
      let neff, _ = Safe_typing.pop_private neff (new_len - old_len) in
      (* Get rid of the fresh side-effects by internalizing them in the term
        itself. Note that this is unsound, because the tactic may have solved
        other goals that were already present during its invocation, so that
        those goals rely on effects that are not present anymore. Hopefully,
        this hack will work in most cases. *)
      let (ans, uctx) = Safe_typing.inline_private_constants env ((ans, Univ.ContextSet.empty), neff) in
      (* Reset the old side-effects *)
      let sigma = Evd.set_side_effects eff sigma in
      let sigma = Evd.merge_universe_context_set ~sideff:true UState.UnivRigid sigma uctx in
      sigma, ans
    else
      sigma, ans
  in
  (* Restore former goals *)
  let _goals, sigma = Evd.pop_future_goals sigma in
  (* Push remaining goals as future_goals which is the only way we
     have to inform the caller that there are goals to collect while
     not being encapsulated in the monad *)
  let sigma = List.fold_right Evd.declare_future_goal goals sigma in
  EConstr.of_constr ans, sigma

(* Abstract internals *)

exception OpenProof

let () = CErrors.register_handler begin function
| OpenProof ->
  let open Pp in
  Some (str "Attempt to save an incomplete proof.")
| _ -> None
end

let rec shrink ctx sign c t accu =
  let open Constr in
  let open Vars in
  match ctx, sign with
  | [], [] -> (c, t, accu)
  | p :: ctx, decl :: sign ->
    if noccurn 1 c && noccurn 1 t then
      let c = subst1 dummy c in
      let t = subst1 dummy t in
      shrink ctx sign c t accu
    else
      let c = Term.mkLambda_or_LetIn p c in
      let t = Term.mkProd_or_LetIn p t in
      let accu = if Context.Rel.Declaration.is_local_assum p
        then EConstr.mkVar (NamedDecl.get_id decl) :: accu
        else accu
      in
      shrink ctx sign c t accu
  | _ -> assert false

(* If [sign] is [x1:T1..xn:Tn], [c] is [fun x1:T1..xn:Tn => c']
    and [t] is [forall x1:T1..xn:Tn, t'], returns a new [c'] and [t'],
    where all non-dependent [xi] are removed, as well as a
    restriction [args] of [x1..xn] such that [c' args] = [c x1..xn] *)
let shrink_entry sign body typ =
  let (ctx, body, typ) = Term.decompose_lambda_prod_n_decls (List.length sign) body typ in
  let (body, typ, args) = shrink ctx sign body typ [] in
  body, typ, args

let build_constant_by_tactic ~name ~sigma ~env ~sign ~poly typ tac =
  let pfenv = Environ.reset_with_named_context sign env in
  let proof = Proof.start ~name ~poly sigma [pfenv, typ] in
  let proof, status = Proof.solve env (Goal_select.select_nth 1) None tac proof in
  let (body, typ, output_ustate) =
    let Proof.{ entry; sigma = evd } = Proof.data proof in
    let body, typ = match Proofview.initial_goals entry with
    | [_, body, typ] -> body, typ
    | _ -> assert false
    in
    let () = if not @@ Proof.is_done proof then raise OpenProof in
    let evd = Evd.minimize_universes evd in
    let to_constr c = match EConstr.to_constr_opt evd c with
    | Some p -> p
    | None -> raise OpenProof
    in
    let body = to_constr body in
    let typ = to_constr typ in
    (body, typ, Evd.ustate evd)
  in
  let univs =
    let used_univs = Vars.universes_of_constr typ in
    let used_univs = Vars.universes_of_constr body ~init:used_univs in
    let uctx = UState.restrict output_ustate used_univs in
    UState.check_univ_decl ~poly uctx UState.default_univ_decl
  in
  (* FIXME: return the locally introduced effects *)
  let { Proof.sigma } = Proof.data proof in
  let sigma = Evd.set_ustate sigma output_ustate in
  (univs, body, typ), status, sigma

let build_by_tactic env ~uctx ~poly ~typ tac =
  let name = Id.of_string "temporary_proof" in
  let sign = Environ.named_context_val env in
  let sigma = Evd.from_ustate uctx in
  (* status doesn't matter: any given up evars can't be in the body/typ
     (we would get OpenProof exception) and we drop the evar part of the evar map *)
  let (univs, body, typ), _status, sigma = build_constant_by_tactic ~name ~env ~sigma ~sign ~poly typ tac in
  let uctx = Evd.ustate sigma in
  (* ignore side effect universes:
     we don't reset the global env in this code path so the side effects are still present
     cf #13271 and discussion in #18874
     (but due to #13324 we still want to inline them) *)
  let effs = Evd.seff_private @@ Evd.eval_side_effects sigma in
  let body, ctx = Safe_typing.inline_private_constants env ((body, Univ.ContextSet.empty), effs) in
  let uctx = UState.merge_universe_context_set ~sideff:true Evd.univ_rigid uctx ctx in
  body, typ, univs, uctx

let build_by_tactic_opt env ~uctx ~poly ~typ tac =
  try Some (build_by_tactic env ~uctx ~poly ~typ tac)
  with OpenProof -> None

let extract_monomorphic = function
  | UState.Monomorphic_entry ctx ->
    Entries.Monomorphic_entry, ctx
  | UState.Polymorphic_entry uctx -> Entries.Polymorphic_entry uctx, Univ.ContextSet.empty

let declare_abstract ~name ~poly ~sign ~secsign ~opaque ~solve_tac env sigma concl =
  let (const, safe, sigma') =
    (* Prevents the nested call to generate the now reserved [name] *)
    let sigma = Evd.avoid_side_effect_label name sigma in
    try build_constant_by_tactic ~name ~poly ~env ~sigma ~sign:secsign concl solve_tac
    with Logic_monad.TacticFailure e as src ->
    (* if the tactic [tac] fails, it reports a [TacticFailure e],
       which is an error irrelevant to the proof system (in fact it
       means that [e] comes from [tac] failing to yield enough
       success). Hence it reraises [e]. *)
    let (_, info) = Exninfo.capture src in
    Exninfo.iraise (e, info)
  in
  let (univs, body, typ) = const in
  let sigma = Evd.drop_new_defined ~original:sigma sigma' in
  let body, typ, args = shrink_entry sign body typ in
  let ts = Environ.oracle env in
  let cst, effs =
    (* No side-effects in the entry, they already exist in the ambient environment *)
    let effs = Evd.eval_side_effects sigma in
    let de, ctx =
      let univ_entry, ctx = extract_monomorphic (fst univs) in
      if not opaque then
        Safe_typing.DefinitionEff { Entries.definition_entry_body = body;
          definition_entry_secctx = None;
          definition_entry_type = Some typ;
          definition_entry_universes = univ_entry;
          definition_entry_inline_code = false;
        }, ctx
      else
        let secctx =
          let env = Global.env () in
          let hyps =
            if List.is_empty (Environ.named_context env) then Id.Set.empty
            else
              let ids_typ = Environ.global_vars_set env typ in
              let vars = Environ.global_vars_set env body in
              Id.Set.union ids_typ vars
          in
          Environ.really_needed env hyps
        in
        Safe_typing.OpaqueEff { Entries.opaque_entry_body = body;
          opaque_entry_secctx = secctx;
          opaque_entry_type = typ;
          opaque_entry_universes = univ_entry;
        },
        ctx
    in
    Evd.push_side_effects ~ts name de ctx effs
  in
  let sigma = Evd.emit_side_effects effs sigma in
  let inst = match univs with
  | UState.Monomorphic_entry _, _ -> UVars.Instance.empty
  | UState.Polymorphic_entry uctx, _ -> UVars.UContext.instance uctx
  in
  let lem = EConstr.of_constr (Constr.mkConstU (cst, inst)) in
  sigma, lem, args, safe
