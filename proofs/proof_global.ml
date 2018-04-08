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
open Context

module NamedDecl = Context.Named.Declaration

(*** Proof Global Environment ***)

(* Extra info on proofs. *)
type lemma_possible_guards = int list list

type proof_object = {
  id : Names.Id.t;
  entries : Safe_typing.private_constants Entries.definition_entry list;
  persistence : Decl_kinds.goal_kind;
  universes: UState.t;
}

type opacity_flag = Opaque | Transparent

type proof_ending =
  | Admitted of Names.Id.t * Decl_kinds.goal_kind * Entries.parameter_entry * UState.t
  | Proved of opacity_flag *
              lident option *
              proof_object

type proof_terminator = proof_ending -> unit
type closed_proof = proof_object * proof_terminator

type pstate = {
  terminator : proof_terminator CEphemeron.key;
  endline_tactic : Genarg.glob_generic_argument option;
  section_vars : Constr.named_context option;
  proof : Proof.t;
  universe_decl: UState.universe_decl;
  strength : Decl_kinds.goal_kind;
}

(* The head of [t] is the actual current proof, the other ones are
   to be resumed when the current proof is closed or aborted. *)
type t = pstate * pstate list

let pstate_map f (pf, pfl) = (f pf, List.map f pfl)

let make_terminator f = f
let apply_terminator f = f

(* combinators for the current_proof lists *)
let push ~ontop a =
  match ontop with
  | None -> a , []
  | Some (l,ls) -> a, (l :: ls)

(*** Proof Global manipulation ***)

let get_all_proof_names (pf : t) =
  let (pn, pns) = pstate_map Proof.(function pf -> (data pf.proof).name) pf in
  pn :: pns

let give_me_the_proof (ps,_) = ps.proof
let get_current_proof_name (ps,_) = (Proof.data ps.proof).Proof.name
let get_current_persistence (ps,_) = ps.strength

let with_current_proof f (ps, psl) =
  let et =
    match ps.endline_tactic with
    | None -> Proofview.tclUNIT ()
    | Some tac ->
      let open Geninterp in
      let ist = { lfun = Id.Map.empty; extra = TacStore.empty } in
      let Genarg.GenArg (Genarg.Glbwit tag, tac) = tac in
      let tac = Geninterp.interp tag ist tac in
      Ftactic.run tac (fun _ -> Proofview.tclUNIT ())
  in
  let (newpr,ret) = f et ps.proof in
  let ps = { ps with proof = newpr } in
  (ps, psl), ret

let simple_with_current_proof f pf =
  let p, () = with_current_proof (fun t p -> f t p , ()) pf in p

let compact_the_proof pf = simple_with_current_proof (fun _ -> Proof.compact) pf

(* Sets the tactic to be used when a tactic line is closed with [...] *)
let set_endline_tactic tac (ps, psl) =
  { ps with endline_tactic = Some tac }, psl

let pf_name_eq id ps =
  let Proof.{ name } = Proof.data ps.proof in
  Id.equal name id

let discard {CAst.loc;v=id} (ps, psl) =
  match List.filter (fun pf -> not (pf_name_eq id pf)) (ps :: psl) with
  | [] -> None
  | ps :: psl -> Some (ps, psl)

let discard_current (ps, psl) =
  if List.is_empty psl then None else Some List.(hd psl, tl psl)

(** [start_proof sigma id pl str goals terminator] starts a proof of name
    [id] with goals [goals] (a list of pairs of environment and
    conclusion); [str] describes what kind of theorem/definition this
    is (spiwack: for potential printing, I believe is used only by
    closing commands and the xml plugin); [terminator] is used at the
    end of the proof to close the proof. The proof is started in the
    evar map [sigma] (which can typically contain universe
    constraints), and with universe bindings pl. *)
let start_proof ~ontop sigma name ?(pl=UState.default_univ_decl) kind goals terminator =
  let initial_state = {
    terminator = CEphemeron.create terminator;
    proof = Proof.start ~name ~poly:(pi2 kind) sigma goals;
    endline_tactic = None;
    section_vars = None;
    universe_decl = pl;
    strength = kind } in
  push ~ontop initial_state

let start_dependent_proof ~ontop name ?(pl=UState.default_univ_decl) kind goals terminator =
  let initial_state = {
    terminator = CEphemeron.create terminator;
    proof = Proof.dependent_start ~name ~poly:(pi2 kind) goals;
    endline_tactic = None;
    section_vars = None;
    universe_decl = pl;
    strength = kind } in
  push ~ontop initial_state

let get_used_variables (pf,_) = pf.section_vars
let get_universe_decl (pf,_) = pf.universe_decl

let set_used_variables (ps,psl) l =
  let open Context.Named.Declaration in
  let env = Global.env () in
  let ids = List.fold_right Id.Set.add l Id.Set.empty in
  let ctx = Environ.keep_hyps env ids in
  let ctx_set =
    List.fold_right Id.Set.add (List.map NamedDecl.get_id ctx) Id.Set.empty in
  let vars_of = Environ.global_vars_set in
  let aux env entry (ctx, all_safe as orig) =
    match entry with
    | LocalAssum ({binder_name=x},_) ->
       if Id.Set.mem x all_safe then orig
       else (ctx, all_safe)
    | LocalDef ({binder_name=x},bo, ty) as decl ->
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
  (ctx, []), ({ ps with section_vars = Some ctx}, psl)

let get_open_goals (ps, _) =
  let Proof.{ goals; stack; shelf } = Proof.data ps.proof in
  List.length goals +
  List.fold_left (+) 0
    (List.map (fun (l1,l2) -> List.length l1 + List.length l2) stack) +
  List.length shelf

type closed_proof_output = (Constr.t * Safe_typing.private_constants) list * UState.t

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
  let { section_vars; proof; terminator; universe_decl; strength } = ps in
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
  let entries = Future.map2 entry_fn fpl Proofview.(initial_goals entry) in
  { id = name; entries = entries; persistence = strength;
    universes },
  fun pr_ending -> CEphemeron.get terminator pr_ending

let return_proof ?(allow_partial=false) (ps,_) =
 let { proof } = ps in
 if allow_partial then begin
  let proofs = Proof.partial_proof proof in
  let Proof.{sigma=evd} = Proof.data proof in
  let eff = Evd.eval_side_effects evd in
  (* ppedrot: FIXME, this is surely wrong. There is no reason to duplicate
     side-effects... This may explain why one need to uniquize side-effects
     thereafter... *)
  let proofs = List.map (fun c -> EConstr.Unsafe.to_constr c, eff) proofs in
    proofs, Evd.evar_universe_context evd
 end else
  let Proof.{name=pid;entry} = Proof.data proof in
  let initial_goals = Proofview.initial_goals entry in
  let evd = Proof.return ~pid proof in
  let eff = Evd.eval_side_effects evd in
  let evd = Evd.minimize_universes evd in
  (* ppedrot: FIXME, this is surely wrong. There is no reason to duplicate
     side-effects... This may explain why one need to uniquize side-effects
     thereafter... *)
  let proof_opt c =
    match EConstr.to_constr_opt evd c with
    | Some p -> p
    | None -> CErrors.user_err Pp.(str "Some unresolved existential variables remain")
  in
  let proofs =
    List.map (fun (c, _) -> (proof_opt c, eff)) initial_goals in
    proofs, Evd.evar_universe_context evd

let close_future_proof ~opaque ~feedback_id (ps, psl) proof =
  close_proof ~opaque ~keep_body_ucst_separate:true ~feedback_id ~now:false proof ps

let close_proof ~opaque ~keep_body_ucst_separate fix_exn (ps, psl) =
  close_proof ~opaque ~keep_body_ucst_separate ~now:true
    (Future.from_val ~fix_exn (return_proof (ps,psl))) ps

(** Gets the current terminator without checking that the proof has
    been completed. Useful for the likes of [Admitted]. *)
let get_terminator (ps, _) = CEphemeron.get ps.terminator
let set_terminator hook (ps, psl) =
  { ps with terminator = CEphemeron.create hook }, psl

let copy_terminators ~src ~tgt =
  let (ps, psl), (ts,tsl) = src, tgt in
  assert(List.length psl = List.length tsl);
  {ts with terminator = ps.terminator}, List.map2 (fun op p -> { p with terminator = op.terminator }) psl tsl

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

