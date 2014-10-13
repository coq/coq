(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Term
open Vars
open Context

(* This module implements the abstract interface to goals *)
(* A general invariant of the module, is that a goal whose associated
   evar is defined in the current evar_map, should not be accessed. *)

(* type of the goals *)
type goal = Evd.evar

let pr_goal e = str "GOAL:" ++ Pp.int (Evar.repr e)

let uid e = string_of_int (Evar.repr e)
let get_by_uid u = Evar.unsafe_of_int (int_of_string u)

(* [advance sigma g] returns [Some g'] if [g'] is undefined and
    is the current avatar of [g] (for instance [g] was changed by [clear]
    into [g']). It returns [None] if [g] has been (partially) solved. *)
(* spiwack: [advance] is probably performance critical, and the good
   behaviour of its definition may depend sensitively to the actual
   definition of [Evd.find]. Currently, [Evd.find] starts looking for
   a value in the heap of undefined variable, which is small. Hence in
   the most common case, where [advance] is applied to an unsolved
   goal ([advance] is used to figure if a side effect has modified the
   goal) it terminates quickly. *)
let rec advance sigma g =
  let evi = Evd.find sigma g in
  match evi.Evd.evar_body with
  | Evd.Evar_empty -> Some g
  | Evd.Evar_defined v ->
      if Option.default false (Evd.Store.get evi.Evd.evar_extra Evarutil.cleared) then
        let (e,_) = Term.destEvar v in
        advance sigma e
      else
        None

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
    let hyps = Environ.named_context_of_val (hyps evars gl) in
    Environ.val_of_named_context (Evarutil.nf_named_context_evar evars hyps)

  (* Access to ".evar_concl" *)
  let concl evars gl =
    let evi = Evd.find evars gl in
    evi.Evd.evar_concl

  (* Access to ".evar_extra" *)
  let extra evars gl =
    let evi = Evd.find evars gl in
    evi.Evd.evar_extra

  (* Old style mk_goal primitive *)
  let mk_goal evars hyps concl extra =
    let evi = { Evd.evar_hyps = hyps;
		Evd.evar_concl = concl;
		Evd.evar_filter = Evd.Filter.identity;
		Evd.evar_body = Evd.Evar_empty;
		Evd.evar_source = (Loc.ghost,Evar_kinds.GoalEvar);
		Evd.evar_candidates = None;
		Evd.evar_extra = extra }
    in
    let evi = Typeclasses.mark_unresolvable evi in
    let (evars, evk) = Evarutil.new_pure_evar_full evars evi in
    let ctxt = Environ.named_context_of_val hyps in
    let inst = Array.map_of_list (fun (id, _, _) -> mkVar id) ctxt in
    let ev = Term.mkEvar (evk,inst) in
    (evk, ev, evars)

  (* Instantiates a goal with an open term *)
  let partial_solution sigma evk c =
    Evd.define evk c sigma

  (* Instantiates a goal with an open term, using name of goal for evk' *)
  let partial_solution_to sigma evk evk' c =
    let id = Evd.evar_ident evk sigma in
    Evd.rename evk' id (Evd.define evk c sigma)

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
      List.fold_right Environ.push_named_context_val extra_hyps hyps in
    let filter = evi.Evd.evar_filter in
    let new_filter = Evd.Filter.extend (List.length extra_hyps) filter in
    let new_evi =
      { evi with Evd.evar_hyps = new_hyps; Evd.evar_filter = new_filter } in
    let new_evi = Typeclasses.mark_unresolvable new_evi in
    let (new_sigma, evk) = Evarutil.new_pure_evar_full Evd.empty new_evi in
    { Evd.it = evk ; sigma = new_sigma; }

  (* Used by the compatibility layer and typeclasses *)
  let nf_evar sigma gl =
    let evi = Evd.find sigma gl in
    let evi = Evarutil.nf_evar_info sigma evi in
    let sigma = Evd.add sigma gl evi in
    (gl, sigma)

  (* Goal represented as a type, doesn't take into account section variables *)
  let abstract_type sigma gl =
    let (gl,sigma) = nf_evar sigma gl in
    let env = env sigma gl in
    let genv = Global.env () in
    let is_proof_var decl =
      try ignore (Environ.lookup_named (Util.pi1 decl) genv); false
      with Not_found -> true in
    Environ.fold_named_context_reverse (fun t decl ->
					  if is_proof_var decl then
					    mkNamedProd_or_LetIn decl t
					  else
					    t
				       ) ~init:(concl sigma gl) env

end
