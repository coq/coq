(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Proofview.Notations
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

let extract_prefix env info =
  let ctx1 = List.rev (EConstr.named_context env) in
  let ctx2 = List.rev (Evd.evar_context info) in
  let rec share l1 l2 accu = match l1, l2 with
  | d1 :: l1, d2 :: l2 ->
    if d1 == d2 then share l1 l2 (d1 :: accu)
    else (accu, d2 :: l2)
  | _ -> (accu, l2)
  in
  share ctx1 ctx2 []

let typecheck_evar ev env sigma =
  let info = Evd.find sigma ev in
  (** Typecheck the hypotheses. *)
  let type_hyp (sigma, env) decl =
    let t = NamedDecl.get_type decl in
    let sigma, _ = Typing.sort_of env sigma t in
    let sigma = match decl with
    | LocalAssum _ -> sigma
    | LocalDef (_,body,_) -> Typing.check env sigma body t
    in
    (sigma, EConstr.push_named decl env)
  in
  let (common, changed) = extract_prefix env info in
  let env = Environ.reset_with_named_context (EConstr.val_of_named_context common) env in
  let (sigma, env) = List.fold_left type_hyp (sigma, env) changed in
  (** Typecheck the conclusion *)
  let sigma, _ = Typing.sort_of env sigma (Evd.evar_concl info) in
  sigma

let (pr_constrv,pr_constr) =
  Hook.make ~default:(fun _env _sigma _c -> Pp.str"<constr>") ()

(* Get the side-effect's constant declarations to update the monad's
  * environmnent *)
let add_if_undefined env eff =
  let open Entries in
  try ignore(Environ.lookup_constant eff.seff_constant env); env
  with Not_found -> Environ.add_constant eff.seff_constant eff.seff_body env

(* Add the side effects to the monad's environment, if not already done. *)
let add_side_effects env eff =
  List.fold_left add_if_undefined env eff

let generic_refine ~typecheck f gl =
  let sigma = Proofview.Goal.sigma gl in
  let env = Proofview.Goal.env gl in
  let concl = Proofview.Goal.concl gl in
  let state = Proofview.Goal.state gl in
  (** Save the [future_goals] state to restore them after the
      refinement. *)
  let prev_future_goals = Evd.save_future_goals sigma in
  (** Create the refinement term *)
  Proofview.Unsafe.tclEVARS (Evd.reset_future_goals sigma) >>= fun () ->
  f >>= fun (v, c) ->
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.V82.wrap_exceptions begin fun () ->
  let evs = Evd.save_future_goals sigma in
  (** Redo the effects in sigma in the monad's env *)
  let privates_csts = Evd.eval_side_effects sigma in
  let sideff = Safe_typing.side_effects_of_private_constants privates_csts in
  let env = add_side_effects env sideff in
  (** Check that the introduced evars are well-typed *)
  let fold accu ev = typecheck_evar ev env accu in
  let sigma = if typecheck then Evd.fold_future_goals fold sigma evs else sigma in
  (** Check that the refined term is typesafe *)
  let sigma = if typecheck then Typing.check env sigma c concl else sigma in
  (** Check that the goal itself does not appear in the refined term *)
  let self = Proofview.Goal.goal gl in
  let _ =
    if not (Evarutil.occur_evar_upto sigma self c) then ()
    else Pretype_errors.error_occur_check env sigma self c
  in
  (** Restore the [future goals] state. *)
  let sigma = Evd.restore_future_goals sigma prev_future_goals in
  (** Select the goals *)
  let evs = Evd.map_filter_future_goals (Proofview.Unsafe.advance sigma) evs in
  let comb,shelf,given_up,evkmain = Evd.dispatch_future_goals evs in
  (** Proceed to the refinement *)
  let sigma = match Proofview.Unsafe.advance sigma self with
  | None ->
    (** Nothing to do, the goal has been solved by side-effect *)
    sigma
  | Some self ->
    match evkmain with
    | None -> Evd.define self c sigma
    | Some evk ->
        let id = Evd.evar_ident self sigma in
        let sigma = Evd.define self c sigma in
        match id with
        | None -> sigma
        | Some id -> Evd.rename evk id sigma
  in
  (** Mark goals *)
  let sigma = CList.fold_left Proofview.Unsafe.mark_as_goal sigma comb in
  let comb = CList.map (fun x -> Proofview.goal_with_state x state) comb in
  let trace () = Pp.(hov 2 (str"simple refine"++spc()++
                            Hook.get pr_constrv env sigma (EConstr.Unsafe.to_constr c))) in
  Proofview.Trace.name_tactic trace (Proofview.tclUNIT v) >>= fun v ->
  Proofview.Unsafe.tclSETENV (Environ.reset_context env) <*>
  Proofview.Unsafe.tclEVARS sigma <*>
  Proofview.Unsafe.tclSETGOALS comb <*>
  Proofview.Unsafe.tclPUTSHELF shelf <*>
  Proofview.Unsafe.tclPUTGIVENUP given_up <*>
  Proofview.tclUNIT v
  end

let lift c =
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.V82.wrap_exceptions begin fun () ->
  let (sigma, c) = c sigma in
  Proofview.Unsafe.tclEVARS sigma >>= fun () ->
  Proofview.tclUNIT c
  end

let make_refine_enter ~typecheck f gl = generic_refine ~typecheck (lift f) gl

let refine_one ~typecheck f =
  Proofview.Goal.enter_one (make_refine_enter ~typecheck f)

let refine ~typecheck f =
  let f evd =
    let (evd,c) = f evd in (evd,((), c))
  in
  Proofview.Goal.enter (make_refine_enter ~typecheck f)

(** Useful definitions *)

let with_type env evd c t =
  let my_type = Retyping.get_type_of env evd c in
  let j = Environ.make_judge c my_type in
  let (evd,j') =
    Coercion.inh_conv_coerce_to true env evd j t
  in
  evd , j'.Environ.uj_val

let refine_casted ~typecheck f = Proofview.Goal.enter begin fun gl ->
  let concl = Proofview.Goal.concl gl in
  let env = Proofview.Goal.env gl in
  let f h =
    let (h, c) = f h in
    with_type env h c concl
  in
  refine ~typecheck f
end

(** {7 solve_constraints}

  Ensure no remaining unification problems are left. Run at every "." by default. *)

let solve_constraints =
  let open Proofview in
  tclENV >>= fun env -> tclEVARMAP >>= fun sigma ->
   try let sigma = Evarconv.solve_unif_constraints_with_heuristics env sigma in
       Unsafe.tclEVARSADVANCE sigma
   with e -> tclZERO e
