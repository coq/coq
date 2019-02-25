(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(***********************************************************************)
(*                                                                     *)
(*      This module defines proof facilities relevant to the           *)
(*      toplevel. In particular it defines the global proof            *)
(*      environment.                                                   *)
(*                                                                     *)
(***********************************************************************)

open Util
open Names

module NamedDecl = Context.Named.Declaration

(*** Proof Global Environment ***)

type proof_object = {
  id : Names.Id.t;
  entry : Safe_typing.private_constants Entries.definition_entry;
  persistence : Decl_kinds.goal_kind;
  universes: UState.t;
}

type opacity_flag = Opaque | Transparent

type t =
  { endline_tactic : Genarg.glob_generic_argument option
  ; section_vars : Constr.named_context option
  ; proof : Proof.t
  ; universe_decl: UState.universe_decl
  ; strength : Decl_kinds.goal_kind
  }

(*** Proof Global manipulation ***)

let give_me_the_proof ps = ps.proof
let get_current_proof_name ps = (Proof.data ps.proof).Proof.name
let get_current_persistence ps = ps.strength

let with_current_proof f ps =
  let et =
    match ps.endline_tactic with
    | None -> Proofview.tclUNIT ()
    | Some tac ->
      let open Geninterp in
      let ist = { lfun = Id.Map.empty; poly = pi2 ps.strength; extra = TacStore.empty } in
      let Genarg.GenArg (Genarg.Glbwit tag, tac) = tac in
      let tac = Geninterp.interp tag ist tac in
      Ftactic.run tac (fun _ -> Proofview.tclUNIT ())
  in
  let (newpr,ret) = f et ps.proof in
  let ps = { ps with proof = newpr } in
  ps, ret

let simple_with_current_proof f pf =
  let p, () = with_current_proof (fun t p -> f t p , ()) pf in p

let compact_the_proof pf = simple_with_current_proof (fun _ -> Proof.compact) pf

(* Sets the tactic to be used when a tactic line is closed with [...] *)
let set_endline_tactic tac ps =
  { ps with endline_tactic = Some tac }

(** [start_proof sigma id pl str goals] starts a proof of name
    [id] with goals [goals] (a list of pairs of environment and
    conclusion); [str] describes what kind of theorem/definition this
    is (spiwack: for potential printing, I believe is used only by
    closing commands and the xml plugin); [terminator] is used at the
    end of the proof to close the proof. The proof is started in the
    evar map [sigma] (which can typically contain universe
    constraints), and with universe bindings pl. *)
let start_proof sigma name ?(pl=UState.default_univ_decl) kind goal =
  let initial_state = {
    proof = Proof.start ~name ~poly:(pi2 kind) sigma goal;
    endline_tactic = None;
    section_vars = None;
    universe_decl = pl;
    strength = kind } in
  initial_state

let get_used_variables pf = pf.section_vars
let get_universe_decl pf = pf.universe_decl

let set_used_variables ps l =
  let open Context.Named.Declaration in
  let env = Global.env () in
  let ids = List.fold_right Id.Set.add l Id.Set.empty in
  let ctx = Environ.keep_hyps env ids in
  let ctx_set =
    List.fold_right Id.Set.add (List.map NamedDecl.get_id ctx) Id.Set.empty in
  let vars_of = Environ.global_vars_set in
  let aux env entry (ctx, all_safe as orig) =
    match entry with
    | LocalAssum (x,_) ->
       if Id.Set.mem x all_safe then orig
       else (ctx, all_safe)
    | LocalDef (x,bo, ty) as decl ->
       if Id.Set.mem x all_safe then orig else
       let vars = Id.Set.union (vars_of env bo) (vars_of env ty) in
       if Id.Set.subset vars all_safe
       then (decl :: ctx, Id.Set.add x all_safe)
       else (ctx, all_safe) in
  let ctx, _ =
    Environ.fold_named_context aux env ~init:(ctx,ctx_set) in
  if not (Option.is_empty ps.section_vars) then
    CErrors.user_err Pp.(str "Used section variables can be declared only once");
  (* EJGA: This is always empty thus we should modify the type *)
  (ctx, []), { ps with section_vars = Some ctx}

let get_open_goals ps =
  let Proof.{ goals; stack; shelf } = Proof.data ps.proof in
  List.length goals +
  List.fold_left (+) 0
    (List.map (fun (l1,l2) -> List.length l1 + List.length l2) stack) +
  List.length shelf

let take_single_proof l = match l with
  | [p] -> p
  | _ ->
    CErrors.anomaly Pp.(str "proof engine returned more than one proof term")

type closed_proof_output = (Constr.t * Safe_typing.private_constants) * UState.t

let private_poly_univs =
  let b = ref true in
  let _ = Goptions.(declare_bool_option {
      optdepr = false;
      optname = "use private polymorphic universes for Qed constants";
      optkey = ["Private";"Polymorphic";"Universes"];
      optread = (fun () -> !b);
      optwrite = ((:=) b);
    })
  in
  fun () -> !b

let close_proof ~opaque ~keep_body_ucst_separate ?feedback_id ~now
                (fpl : closed_proof_output Future.computation) ps =
  let { section_vars; proof; universe_decl; strength } = ps in
  let Proof.{ name; poly; entry; initial_euctx } = Proof.data proof in
  let opaque = match opaque with Opaque -> true | Transparent -> false in
  let constrain_variables ctx =
    UState.constrain_variables (fst (UState.context_set initial_euctx)) ctx
  in
  let fpl, univs = Future.split2 fpl in
  let universes = if poly || now then Future.force univs else initial_euctx in
  (* Because of dependent subgoals at the beginning of proofs, we could
     have existential variables in the initial types of goals, we need to
     normalise them for the kernel. *)
  let subst_evar k =
    Proof.in_proof proof (fun m -> Evd.existential_opt_value0 m k) in
  let nf = UnivSubst.nf_evars_and_universes_opt_subst subst_evar
    (UState.subst universes) in

  let make_body =
    if poly || now then
      let make_body t (c, eff) =
        let body = c in
        let allow_deferred =
          not poly && (keep_body_ucst_separate ||
          not (Safe_typing.empty_private_constants = eff))
        in
        let typ = if allow_deferred then t else nf t in
        let used_univs_body = Vars.universes_of_constr body in
        let used_univs_typ = Vars.universes_of_constr typ in
        if allow_deferred then
          let initunivs = UState.univ_entry ~poly initial_euctx in
          let ctx = constrain_variables universes in
          (* For vi2vo compilation proofs are computed now but we need to
             complement the univ constraints of the typ with the ones of
             the body.  So we keep the two sets distinct. *)
          let used_univs = Univ.LSet.union used_univs_body used_univs_typ in
          let ctx_body = UState.restrict ctx used_univs in
          let univs = UState.check_mono_univ_decl ctx_body universe_decl in
          (initunivs, typ), ((body, univs), eff)
        else if poly && opaque && private_poly_univs () then
          let used_univs = Univ.LSet.union used_univs_body used_univs_typ in
          let universes = UState.restrict universes used_univs in
          let typus = UState.restrict universes used_univs_typ in
          let udecl = UState.check_univ_decl ~poly typus universe_decl in
          let ubody = Univ.ContextSet.diff
              (UState.context_set universes)
              (UState.context_set typus)
          in
          (udecl, typ), ((body, ubody), eff)
        else
          (* Since the proof is computed now, we can simply have 1 set of
             constraints in which we merge the ones for the body and the ones
             for the typ. We recheck the declaration after restricting with
             the actually used universes.
             TODO: check if restrict is really necessary now. *)
          let used_univs = Univ.LSet.union used_univs_body used_univs_typ in
          let ctx = UState.restrict universes used_univs in
          let univs = UState.check_univ_decl ~poly ctx universe_decl in
          (univs, typ), ((body, Univ.ContextSet.empty), eff)
      in 
       fun t p -> Future.split2 (Future.chain p (make_body t))
    else
      fun t p ->
        (* Already checked the univ_decl for the type universes when starting the proof. *)
        let univctx = UState.univ_entry ~poly:false universes in
        let t = nf t in
        Future.from_val (univctx, t),
        Future.chain p (fun (pt,eff) ->
          (* Deferred proof, we already checked the universe declaration with
             the initial universes, ensure that the final universes respect
             the declaration as well. If the declaration is non-extensible,
             this will prevent the body from adding universes and constraints. *)
          let univs = Future.force univs in
          let univs = constrain_variables univs in
          let used_univs = Univ.LSet.union
              (Vars.universes_of_constr t)
              (Vars.universes_of_constr pt)
          in
          let univs = UState.restrict univs used_univs in
          let univs = UState.check_mono_univ_decl univs universe_decl in
          (pt,univs),eff)
  in
  let entry_fn p (_, t) =
    let t = EConstr.Unsafe.to_constr t in
    let univstyp, body = make_body t p in
    let univs, typ = Future.force univstyp in
    {Entries.
      const_entry_body = body;
      const_entry_secctx = section_vars;
      const_entry_feedback = feedback_id;
      const_entry_type  = Some typ;
      const_entry_inline_code = false;
      const_entry_opaque = opaque;
      const_entry_universes = univs; }
  in
  let goal = take_single_proof @@ Proofview.initial_goals entry in
  let entry = entry_fn fpl goal in
  { id = name; entry; persistence = strength;  universes }

let return_proof ?(allow_partial=false) ps =
 let { proof } = ps in
 if allow_partial then begin
  let Proof.{sigma=evd} = Proof.data proof in
  let eff = Evd.eval_side_effects evd in
  let proof = take_single_proof @@ Proof.partial_proof proof in
  let proof = EConstr.Unsafe.to_constr proof, eff in
  proof, Evd.evar_universe_context evd
 end else
  let Proof.{name=pid;entry} = Proof.data proof in
  let evd = Proof.return ~pid proof in
  let eff = Evd.eval_side_effects evd in
  let evd = Evd.minimize_universes evd in
  let proof_opt c =
    match EConstr.to_constr_opt evd c with
    | Some p -> p
    | None -> CErrors.user_err Pp.(str "Some unresolved existential variables remain")
  in
  let proof,_ = take_single_proof @@ Proofview.initial_goals entry in
  let proof = proof_opt proof, eff in
  proof, Evd.evar_universe_context evd

let close_future_proof ~opaque ~feedback_id ps proof =
  close_proof ~opaque ~keep_body_ucst_separate:true ~feedback_id ~now:false proof ps

let close_proof ~opaque ~keep_body_ucst_separate fix_exn ps =
  close_proof ~opaque ~keep_body_ucst_separate ~now:true
    (Future.from_val ~fix_exn (return_proof ps)) ps

let update_global_env (pf : t) =
  let res, () =
  with_current_proof (fun _ p ->
        Proof.in_proof p (fun sigma ->
            let tac = Proofview.Unsafe.tclEVARS (Evd.update_sigma_env sigma (Global.env ())) in
            let (p,(status,info)) = Proof.run_tactic (Global.env ()) tac p in
            (p, ()))) pf
  in res

(* XXX: This hook is used to provide a better error w.r.t. bullets,
   however the proof engine [surprise!] knows nothing about bullets so
   here we have a layering violation. The right fix is to modify the
   entry point to handle this and reraise the exception with the
   needed information. *)
(* let _ =
 *   let hook n =
 *     try
 *       let prf = give_me_the_proof pf in
 *       (Proof_bullet.suggest prf)
 *     with NoCurrentProof -> mt ()
 *   in
 *   Proofview.set_nosuchgoals_hook hook *)

