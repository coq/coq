(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Entries
open Environ
open Evd

let refining = Proof_global.there_are_pending_proofs
let check_no_pending_proofs = Proof_global.check_no_pending_proof

let get_current_proof_name = Proof_global.get_current_proof_name
let get_all_proof_names = Proof_global.get_all_proof_names

type lemma_possible_guards = Proof_global.lemma_possible_guards
type universe_binders = Proof_global.universe_binders

let delete_proof = Proof_global.discard
let delete_current_proof = Proof_global.discard_current
let delete_all_proofs = Proof_global.discard_all

let start_proof (id : Id.t) ?pl str sigma hyps c ?init_tac terminator =
  let goals = [ (Global.env_of_context hyps , c) ] in
  Proof_global.start_proof sigma id ?pl str goals terminator;
  let env = Global.env () in
  ignore (Proof_global.with_current_proof (fun _ p ->
    match init_tac with
    | None -> p,(true,[])
    | Some tac -> Proof.run_tactic env tac p))

let cook_this_proof p =
  match p with
  | { Proof_global.id;entries=[constr];persistence;universes } ->
      (id,(constr,universes,persistence))
  | _ -> CErrors.anomaly ~label:"Pfedit.cook_proof" (Pp.str "more than one proof term.")

let cook_proof () =
  cook_this_proof (fst
    (Proof_global.close_proof ~keep_body_ucst_separate:false (fun x -> x)))
let get_pftreestate () =
  Proof_global.give_me_the_proof ()

let set_end_tac tac =
  Proof_global.set_endline_tactic tac

let set_used_variables l =
  Proof_global.set_used_variables l
let get_used_variables () =
  Proof_global.get_used_variables ()

let get_universe_binders () =
  Proof_global.get_universe_binders ()

exception NoSuchGoal
let _ = CErrors.register_handler begin function
  | NoSuchGoal -> CErrors.error "No such goal."
  | _ -> raise CErrors.Unhandled
end
let get_nth_V82_goal i =
  let p = Proof_global.give_me_the_proof () in
  let { it=goals ; sigma = sigma; } = Proof.V82.subgoals p in
  try
          { it=(List.nth goals (i-1)) ; sigma=sigma; }
  with Failure _ -> raise NoSuchGoal
    
let get_goal_context_gen i =
  let { it=goal ; sigma=sigma; } =  get_nth_V82_goal i in
  (sigma, Refiner.pf_env { it=goal ; sigma=sigma; })

let get_goal_context i =
  try get_goal_context_gen i
  with Proof_global.NoCurrentProof -> CErrors.error "No focused proof."
     | NoSuchGoal -> CErrors.error "No such goal."

let get_current_goal_context () =
  try get_goal_context_gen 1
  with Proof_global.NoCurrentProof -> CErrors.error "No focused proof."
     | NoSuchGoal -> 
    (* spiwack: returning empty evar_map, since if there is no goal, under focus,
        there is no accessible evar either *)
    let env = Global.env () in
    (Evd.from_env env, env)

let get_current_context () =
  try get_goal_context_gen 1
  with Proof_global.NoCurrentProof ->
    let env = Global.env () in
    (Evd.from_env env, env)
     | NoSuchGoal ->
        (* No more focused goals ? *)
        let p = get_pftreestate () in
        let evd = Proof.in_proof p (fun x -> x) in
        (evd, Global.env ())

let current_proof_statement () =
  match Proof_global.V82.get_current_initial_conclusions () with
    | (id,([concl],strength)) -> id,strength,concl
    | _ -> CErrors.anomaly ~label:"Pfedit.current_proof_statement" (Pp.str "more than one statement")

let solve ?with_end_tac gi info_lvl tac pr =
  try 
    let tac = match with_end_tac with
      | None -> tac
      | Some etac -> Proofview.tclTHEN tac etac in
    let tac = match info_lvl with
      | None -> tac
      | Some _ -> Proofview.Trace.record_info_trace tac
    in
    let tac = match gi with
      | Vernacexpr.SelectNth i -> Proofview.tclFOCUS i i tac
      | Vernacexpr.SelectList l -> Proofview.tclFOCUSLIST l tac
      | Vernacexpr.SelectId id -> Proofview.tclFOCUSID id tac
      | Vernacexpr.SelectAll -> tac
    in
    let (p,(status,info)) = Proof.run_tactic (Global.env ()) tac pr in
    let () =
      match info_lvl with
      | None -> ()
      | Some i -> Feedback.msg_info (hov 0 (Proofview.Trace.pr_info ~lvl:i info))
    in
    (p,status)
  with
    | Proof_global.NoCurrentProof  -> CErrors.error "No focused proof"
    | CList.IndexOutOfRange ->
        match gi with
	| Vernacexpr.SelectNth i -> let msg = str "No such goal: " ++ int i ++ str "." in
	                            CErrors.errorlabstrm "" msg
        | _ -> assert false

let by tac = Proof_global.with_current_proof (fun _ -> solve (Vernacexpr.SelectNth 1) None tac)

let instantiate_nth_evar_com n com = 
  Proof_global.simple_with_current_proof (fun _ p -> Proof.V82.instantiate_evar n com p)


(**********************************************************************)
(* Shortcut to build a term using tactics *)

open Decl_kinds

let next = let n = ref 0 in fun () -> incr n; !n

let build_constant_by_tactic id ctx sign ?(goal_kind = Global, false, Proof Theorem) typ tac =
  let evd = Evd.from_ctx ctx in
  let terminator = Proof_global.make_terminator (fun _ -> ()) in
  start_proof id goal_kind evd sign typ terminator;
  try
    let status = by tac in
    let _,(const,univs,_) = cook_proof () in
    delete_current_proof ();
    const, status, fst univs
  with reraise ->
    let reraise = CErrors.push reraise in
    delete_current_proof ();
    iraise reraise

let build_by_tactic ?(side_eff=true) env ctx ?(poly=false) typ tac =
  let id = Id.of_string ("temporary_proof"^string_of_int (next())) in
  let sign = val_of_named_context (named_context env) in
  let gk = Global, poly, Proof Theorem in
  let ce, status, univs = build_constant_by_tactic id ctx sign ~goal_kind:gk typ tac in
  let ce =
    if side_eff then Safe_typing.inline_private_constants_in_definition_entry env ce
    else { ce with
      const_entry_body = Future.chain ~pure:true ce.const_entry_body
        (fun (pt, _) -> pt, Safe_typing.empty_private_constants) } in
  let (cb, ctx), se = Future.force ce.const_entry_body in
  let univs' = Evd.merge_context_set Evd.univ_rigid (Evd.from_ctx univs) ctx in
  assert(Safe_typing.empty_private_constants = se);
  cb, status, Evd.evar_universe_context univs'

let refine_by_tactic env sigma ty tac =
  (** Save the initial side-effects to restore them afterwards. We set the
      current set of side-effects to be empty so that we can retrieve the
      ones created during the tactic invocation easily. *)
  let eff = Evd.eval_side_effects sigma in
  let sigma = Evd.drop_side_effects sigma in
  (** Start a proof *)
  let prf = Proof.start sigma [env, ty] in
  let (prf, _) =
    try Proof.run_tactic env tac prf
    with Logic_monad.TacticFailure e as src ->
      (** Catch the inner error of the monad tactic *)
      let (_, info) = CErrors.push src in
      iraise (e, info)
  in
  (** Plug back the retrieved sigma *)
  let sigma = Proof.in_proof prf (fun sigma -> sigma) in
  let ans = match Proof.initial_goals prf with
  | [c, _] -> c
  | _ -> assert false
  in
  let ans = Reductionops.nf_evar sigma ans in
  (** [neff] contains the freshly generated side-effects *)
  let neff = Evd.eval_side_effects sigma in
  (** Reset the old side-effects *)
  let sigma = Evd.drop_side_effects sigma in
  let sigma = Evd.emit_side_effects eff sigma in
  (** Get rid of the fresh side-effects by internalizing them in the term
      itself. Note that this is unsound, because the tactic may have solved
      other goals that were already present during its invocation, so that
      those goals rely on effects that are not present anymore. Hopefully,
      this hack will work in most cases. *)
  let ans = Safe_typing.inline_private_constants_in_constr env ans neff in
  ans, sigma

(**********************************************************************)
(* Support for resolution of evars in tactic interpretation, including
   resolution by application of tactics *)

let implicit_tactic = ref None

let declare_implicit_tactic tac = implicit_tactic := Some tac

let clear_implicit_tactic () = implicit_tactic := None

let solve_by_implicit_tactic env sigma evk =
  let evi = Evd.find_undefined sigma evk in
  match (!implicit_tactic, snd (evar_source evk sigma)) with
  | Some tac, (Evar_kinds.ImplicitArg _ | Evar_kinds.QuestionMark _)
      when
	Context.Named.equal (Environ.named_context_of_val evi.evar_hyps)
	(Environ.named_context env) ->
      let tac = Proofview.tclTHEN tac (Proofview.tclEXTEND [] (Proofview.tclZERO (CErrors.UserError ("",Pp.str"Proof is not complete."))) []) in
      (try
        let (ans, _, _) = 
	  build_by_tactic env (Evd.evar_universe_context sigma) evi.evar_concl tac in
        ans
       with e when Logic.catchable_exception e -> raise Exit)
  | _ -> raise Exit
