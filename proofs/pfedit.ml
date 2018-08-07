(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Names
open Entries
open Environ
open Evd

let use_unification_heuristics_ref = ref true
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Solve unification constraints at every \".\"";
  Goptions.optkey = ["Solve";"Unification";"Constraints"];
  Goptions.optread = (fun () -> !use_unification_heuristics_ref);
  Goptions.optwrite = (fun a -> use_unification_heuristics_ref:=a);
}

let use_unification_heuristics () = !use_unification_heuristics_ref

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

exception NoSuchGoal
let _ = CErrors.register_handler begin function
  | NoSuchGoal -> CErrors.user_err Pp.(str "No such goal.")
  | _ -> raise CErrors.Unhandled
end

let get_nth_V82_goal p i =
  let goals,_,_,_,sigma = Proof.proof p in
  try { it = List.nth goals (i-1) ; sigma }
  with Failure _ -> raise NoSuchGoal

let get_goal_context_gen p i =
  let { it=goal ; sigma=sigma; } = get_nth_V82_goal p i in
  (sigma, Refiner.pf_env { it=goal ; sigma=sigma; })

let get_goal_context i =
  try get_goal_context_gen (Proof_global.give_me_the_proof ()) i
  with Proof_global.NoCurrentProof -> CErrors.user_err Pp.(str "No focused proof.")
     | NoSuchGoal -> CErrors.user_err Pp.(str "No such goal.")

let get_current_goal_context () =
  try get_goal_context_gen (Proof_global.give_me_the_proof ()) 1
  with Proof_global.NoCurrentProof -> CErrors.user_err Pp.(str "No focused proof.")
     | NoSuchGoal -> 
    (* spiwack: returning empty evar_map, since if there is no goal, under focus,
        there is no accessible evar either *)
    let env = Global.env () in
    (Evd.from_env env, env)

let get_current_context ?p () =
  let current_proof_by_default = function
    | Some p -> p
    | None -> Proof_global.give_me_the_proof ()
  in
  try get_goal_context_gen (current_proof_by_default p) 1
  with Proof_global.NoCurrentProof ->
    let env = Global.env () in
    (Evd.from_env env, env)
     | NoSuchGoal ->
        (* No more focused goals ? *)
        let p = (current_proof_by_default p) in
        let evd = Proof.in_proof p (fun x -> x) in
        (evd, Global.env ())

let current_proof_statement () =
  match Proof_global.V82.get_current_initial_conclusions () with
    | (id,([concl],strength)) -> id,strength,concl
    | _ -> CErrors.anomaly ~label:"Pfedit.current_proof_statement" (Pp.str "more than one statement.")

let solve ?with_end_tac gi info_lvl tac pr =
  try 
    let tac = match with_end_tac with
      | None -> tac
      | Some etac -> Proofview.tclTHEN tac etac in
    let tac = match info_lvl with
      | None -> tac
      | Some _ -> Proofview.Trace.record_info_trace tac
    in
    let tac = let open Goal_select in match gi with
      | SelectAlreadyFocused ->
        let open Proofview.Notations in
        Proofview.numgoals >>= fun n ->
        if n == 1 then tac
        else
          let e = CErrors.UserError
              (None,
               Pp.(str "Expected a single focused goal but " ++
                   int n ++ str " goals are focused."))
          in
          Proofview.tclZERO e

      | SelectNth i -> Proofview.tclFOCUS i i tac
      | SelectList l -> Proofview.tclFOCUSLIST l tac
      | SelectId id -> Proofview.tclFOCUSID id tac
      | SelectAll -> tac
    in
    let tac =
      if use_unification_heuristics () then
        Proofview.tclTHEN tac Refine.solve_constraints
      else tac
    in
    let (p,(status,info)) = Proof.run_tactic (Global.env ()) tac pr in
    let () =
      match info_lvl with
      | None -> ()
      | Some i -> Feedback.msg_info (hov 0 (Proofview.Trace.pr_info ~lvl:i info))
    in
    (p,status)
  with
    Proof_global.NoCurrentProof -> CErrors.user_err Pp.(str "No focused proof")

let by tac = Proof_global.with_current_proof (fun _ -> solve (Goal_select.SelectNth 1) None tac)

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
    Proof_global.discard_current ();
    let univs = UState.demote_seff_univs const univs in
    const, status, univs
  with reraise ->
    let reraise = CErrors.push reraise in
    Proof_global.discard_current ();
    iraise reraise

let build_by_tactic ?(side_eff=true) env sigma ?(poly=false) typ tac =
  let id = Id.of_string ("temporary_proof"^string_of_int (next())) in
  let sign = val_of_named_context (named_context env) in
  let gk = Global, poly, Proof Theorem in
  let ce, status, univs =
    build_constant_by_tactic id sigma sign ~goal_kind:gk typ tac in
  let ce =
    if side_eff then Safe_typing.inline_private_constants_in_definition_entry env ce
    else { ce with
      const_entry_body = Future.chain ce.const_entry_body
        (fun (pt, _) -> pt, ()) } in
  let (cb, ctx), () = Future.force ce.const_entry_body in
  let univs = UState.merge ~sideff:side_eff ~extend:true Evd.univ_rigid univs ctx in
  cb, status, univs

let refine_by_tactic env sigma ty tac =
  (** Save the initial side-effects to restore them afterwards. We set the
      current set of side-effects to be empty so that we can retrieve the
      ones created during the tactic invocation easily. *)
  let eff = Evd.eval_side_effects sigma in
  let sigma = Evd.drop_side_effects sigma in
  (** Save the existing goals *)
  let prev_future_goals = save_future_goals sigma in
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
  let (goals,stack,shelf,given_up,sigma) = Proof.proof prf in
  assert (stack = []);
  let ans = match Proof.initial_goals prf with
  | [c, _] -> c
  | _ -> assert false
  in
  let ans = EConstr.to_constr ~abort_on_undefined_evars:false sigma ans in
  (** [neff] contains the freshly generated side-effects *)
  let neff = Evd.eval_side_effects sigma in
  (** Reset the old side-effects *)
  let sigma = Evd.drop_side_effects sigma in
  let sigma = Evd.emit_side_effects eff sigma in
  (** Restore former goals *)
  let sigma = restore_future_goals sigma prev_future_goals in
  (** Push remaining goals as future_goals which is the only way we
      have to inform the caller that there are goals to collect while
      not being encapsulated in the monad *)
  (** Goals produced by tactic "shelve" *)
  let sigma = List.fold_right (Evd.declare_future_goal ~tag:Evd.ToShelve) shelf sigma in
  (** Goals produced by tactic "give_up" *)
  let sigma = List.fold_right (Evd.declare_future_goal ~tag:Evd.ToGiveUp) given_up sigma in
  (** Other goals *)
  let sigma = List.fold_right Evd.declare_future_goal goals sigma in
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

let implicit_tactic = Summary.ref None ~name:"implicit-tactic"

let declare_implicit_tactic tac = implicit_tactic := Some tac

let clear_implicit_tactic () = implicit_tactic := None

let apply_implicit_tactic tac = (); fun env sigma evk ->
  let evi = Evd.find_undefined sigma evk in
  match snd (evar_source evk sigma) with
  | (Evar_kinds.ImplicitArg _ | Evar_kinds.QuestionMark _)
      when
	Context.Named.equal Constr.equal (Environ.named_context_of_val evi.evar_hyps)
	(Environ.named_context env) ->
      let tac = Proofview.tclTHEN tac (Proofview.tclEXTEND [] (Proofview.tclZERO (CErrors.UserError (None,Pp.str"Proof is not complete."))) []) in
      (try
        let c = Evarutil.nf_evars_universes sigma (EConstr.Unsafe.to_constr evi.evar_concl) in
        let c = EConstr.of_constr c in
        if Evarutil.has_undefined_evars sigma c then raise Exit;
        let (ans, _, ctx) =
	  build_by_tactic env (Evd.evar_universe_context sigma) c tac in
        let sigma = Evd.set_universe_context sigma ctx in
        sigma, EConstr.of_constr ans
       with e when Logic.catchable_exception e -> raise Exit)
  | _ -> raise Exit

let solve_by_implicit_tactic () = match !implicit_tactic with
| None -> None
| Some tac -> Some (apply_implicit_tactic tac)
