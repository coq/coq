(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp

module NamedDecl = Context.Named.Declaration

(* This module implements the abstract interface to goals *)
(* A general invariant of the module, is that a goal whose associated
   evar is defined in the current evar_map, should not be accessed. *)

(* type of the goals *)
type goal = Evd.evar

let pr_goal e = str "GOAL:" ++ Pp.int (Evar.repr e)

let uid e = string_of_int (Evar.repr e)
let get_by_uid u = Evar.unsafe_of_int (int_of_string u)

(* Layer to implement v8.2 tactic engine ontop of the new architecture.
   Types are different from what they used to be due to a change of the
   internal types. *)
module V82 = struct

  (* Old style env primitive *)
  let env evars gl =
    let evi = Evd.find evars gl in
    Evd.evar_filtered_env evi

  (* Old style hyps primitive *)
  let hyps evars gl =
    let evi = Evd.find evars gl in
    Evd.evar_filtered_hyps evi

  (* same as [hyps], but ensures that existential variables are
     normalised. *)
  let nf_hyps evars gl =
    let ctxt = hyps evars gl in
    let hyps = Environ.named_context_of_val ctxt in
    Environ.val_of_named_context (Evarutil.nf_named_context_evar evars hyps)
                                 (Environ.named_context_private_ids ctxt)

  (* Access to ".evar_concl" *)
  let concl evars gl =
    let evi = Evd.find evars gl in
    EConstr.of_constr evi.Evd.evar_concl

  (* Access to ".private" *)
  let private_ids evars gl =
    let evi = Evd.find evars gl in
    evi.Evd.evar_private

  (* Access to ".evar_extra" *)
  let extra evars gl =
    let evi = Evd.find evars gl in
    evi.Evd.evar_extra

  (* Old style mk_goal primitive *)
  let mk_goal evars hyps private_ids concl extra =
    (* A goal created that way will not be used by refine and will not
       be shelved. It must not appear as a future_goal, so the future
       goals are restored to their initial value after the evar is
       created. *)
    let concl = EConstr.Unsafe.to_constr concl in
    let prev_future_goals = Evd.future_goals evars in
    let prev_principal_goal = Evd.principal_future_goal evars in
    let evi = { Evd.evar_hyps = hyps;
		Evd.evar_concl = concl;
		Evd.evar_filter = Evd.Filter.identity;
		Evd.evar_private = private_ids;
		Evd.evar_concl_user_names = Names.Id.Set.empty;
		Evd.evar_body = Evd.Evar_empty;
		Evd.evar_source = (Loc.tag Evar_kinds.GoalEvar);
		Evd.evar_candidates = None;
		Evd.evar_extra = extra }
    in
    let evi = Typeclasses.mark_unresolvable evi in
    let (evars, evk) = Evarutil.new_pure_evar_full evars evi in
    let evars = Evd.restore_future_goals evars prev_future_goals prev_principal_goal in
    let ctxt = Environ.named_context_of_val hyps in
    let inst = Array.map_of_list (NamedDecl.get_id %> EConstr.mkVar) ctxt in
    let ev = EConstr.mkEvar (evk,inst) in
    (evk, ev, evars)

  (* Instantiates a goal with an open term *)
  let partial_solution sigma evk c =
    (* Check that the goal itself does not appear in the refined term *)
    let _ =
      if not (Evarutil.occur_evar_upto sigma evk c) then ()
      else Pretype_errors.error_occur_check Environ.empty_env sigma evk c
    in
    Evd.define evk (EConstr.Unsafe.to_constr c) sigma

  (* Instantiates a goal with an open term, using name of goal for evk' *)
  let partial_solution_to sigma evk evk' c =
    let id = Evd.evar_ident evk sigma in
    let sigma = partial_solution sigma evk c in
    match id with
    | None -> sigma
    | Some id -> Evd.rename evk' id sigma

  (* Parts of the progress tactical *)
  let same_goal evars1 gl1 evars2 gl2 =
    let evi1 = Evd.find evars1 gl1 in
    let evi2 = Evd.find evars2 gl2 in
    Term.eq_constr evi1.Evd.evar_concl evi2.Evd.evar_concl &&
    Environ.eq_named_context_val evi1.Evd.evar_hyps evi2.Evd.evar_hyps

  let weak_progress glss gls =
    match glss.Evd.it with
    | [ g ] -> not (same_goal glss.Evd.sigma g gls.Evd.sigma gls.Evd.it)
    | _ -> true

  let progress glss gls =
    weak_progress glss gls
    (* spiwack: progress normally goes like this:
    (Evd.progress_evar_map gls.Evd.sigma glss.Evd.sigma) || (weak_progress glss gls)
       This is immensly slow in the current implementation. Maybe we could
       reimplement progress_evar_map with restricted folds like "fold_undefined",
       with a good implementation of them.
    *)

  (* Used for congruence closure  *)
  let new_goal_with sigma gl extra_hyps =
    let evi = Evd.find sigma gl in
    let hyps = evi.Evd.evar_hyps in
    let new_hyps =
      List.fold_right (fun d -> Environ.push_named_context_val d true) extra_hyps hyps in
    let filter = evi.Evd.evar_filter in
    let new_filter = Evd.Filter.extend (List.length extra_hyps) filter in
    let new_evi =
      { evi with Evd.evar_hyps = new_hyps; Evd.evar_filter = new_filter } in
    let new_evi = Typeclasses.mark_unresolvable new_evi in
    let (sigma, evk) = Evarutil.new_pure_evar_full Evd.empty new_evi in
    { Evd.it = evk ; sigma = sigma; }

  (* Used by the compatibility layer and typeclasses *)
  let nf_evar sigma gl =
    let evi = Evd.find sigma gl in
    let evi = Evarutil.nf_evar_info sigma evi in
    let sigma = Evd.add sigma gl evi in
    (gl, sigma)

  (* Goal represented as a type, doesn't take into account section variables *)
  let abstract_type sigma gl =
    let open EConstr in
    let (gl,sigma) = nf_evar sigma gl in
    let env = env sigma gl in
    let genv = Global.env () in
    let is_proof_var decl =
      try ignore (Environ.lookup_named (NamedDecl.get_id decl) genv); false
      with Not_found -> true in
    Environ.fold_named_context_reverse (fun t decl ->
					  if is_proof_var decl then
                                            let decl = Termops.map_named_decl EConstr.of_constr decl in
					    mkNamedProd_or_LetIn decl t
					  else
					    t
				       ) ~init:(concl sigma gl) env

end
