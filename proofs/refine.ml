(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Sigma.Notations
open Proofview.Notations
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

let extract_prefix env info =
  let ctx1 = List.rev (Environ.named_context env) in
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
    let t = EConstr.of_constr (NamedDecl.get_type decl) in
    let evdref = ref sigma in
    let _ = Typing.e_sort_of env evdref t in
    let () = match decl with
    | LocalAssum _ -> ()
    | LocalDef (_,body,_) -> Typing.e_check env evdref (EConstr.of_constr body) t
    in
    (!evdref, Environ.push_named decl env)
  in
  let (common, changed) = extract_prefix env info in
  let env = Environ.reset_with_named_context (Environ.val_of_named_context common) env in
  let (sigma, env) = List.fold_left type_hyp (sigma, env) changed in
  (** Typecheck the conclusion *)
  let evdref = ref sigma in
  let _ = Typing.e_sort_of env evdref (EConstr.of_constr (Evd.evar_concl info)) in
  !evdref

let typecheck_proof c concl env sigma =
  let evdref = ref sigma in
  let () = Typing.e_check env evdref c concl in
  !evdref

let (pr_constrv,pr_constr) =
  Hook.make ~default:(fun _env _sigma _c -> Pp.str"<constr>") ()

(* Get the side-effect's constant declarations to update the monad's
  * environmnent *)
let add_if_undefined kn cb env =
  try ignore(Environ.lookup_constant kn env); env
  with Not_found -> Environ.add_constant kn cb env

(* Add the side effects to the monad's environment, if not already done. *)
let add_side_effect env = function
  | { Entries.eff = Entries.SEsubproof (kn, cb, eff_env) } ->
    add_if_undefined kn cb env
  | { Entries.eff = Entries.SEscheme (l,_) } ->
    List.fold_left (fun env (_,kn,cb,eff_env) ->
        add_if_undefined kn cb env) env l

let add_side_effects env effects =
  List.fold_left (fun env eff -> add_side_effect env eff) env effects

let make_refine_enter ?(unsafe = true) f =
  { enter = fun gl ->
  let gl = Proofview.Goal.assume gl in
  let sigma = Proofview.Goal.sigma gl in
  let sigma = Sigma.to_evar_map sigma in
  let env = Proofview.Goal.env gl in
  let concl = Proofview.Goal.concl gl in
  let concl = EConstr.of_constr concl in
  (** Save the [future_goals] state to restore them after the
      refinement. *)
  let prev_future_goals = Evd.future_goals sigma in
  let prev_principal_goal = Evd.principal_future_goal sigma in
  (** Create the refinement term *)
  let ((v,c), sigma) = Sigma.run (Evd.reset_future_goals sigma) f in
  let evs = Evd.future_goals sigma in
  let evkmain = Evd.principal_future_goal sigma in
  (** Redo the effects in sigma in the monad's env *)
  let privates_csts = Evd.eval_side_effects sigma in
  let sideff = Safe_typing.side_effects_of_private_constants privates_csts in
  let env = add_side_effects env sideff in
  (** Check that the introduced evars are well-typed *)
  let fold accu ev = typecheck_evar ev env accu in
  let sigma = if unsafe then sigma else CList.fold_left fold sigma evs in
  (** Check that the refined term is typesafe *)
  let sigma = if unsafe then sigma else typecheck_proof c concl env sigma in
  (** Check that the goal itself does not appear in the refined term *)
  let self = Proofview.Goal.goal gl in
  let _ =
    if not (Evarutil.occur_evar_upto sigma self c) then ()
    else Pretype_errors.error_occur_check env sigma self c
  in
  (** Proceed to the refinement *)
  let c = EConstr.Unsafe.to_constr c in
  let sigma = match evkmain with
    | None -> Evd.define self c sigma
    | Some evk ->
        let id = Evd.evar_ident self sigma in
        let sigma = Evd.define self c sigma in
        match id with
        | None -> sigma
        | Some id -> Evd.rename evk id sigma
  in
  (** Restore the [future goals] state. *)
  let sigma = Evd.restore_future_goals sigma prev_future_goals prev_principal_goal in
  (** Select the goals *)
  let comb = CList.map_filter (Proofview.Unsafe.advance sigma) (CList.rev evs) in
  let sigma = CList.fold_left Proofview.Unsafe.mark_as_goal sigma comb in
  let trace () = Pp.(hov 2 (str"simple refine"++spc()++ Hook.get pr_constrv env sigma c)) in
  Proofview.Trace.name_tactic trace (Proofview.tclUNIT v) >>= fun v ->
  Proofview.Unsafe.tclSETENV (Environ.reset_context env) <*>
  Proofview.Unsafe.tclEVARS sigma <*>
  Proofview.Unsafe.tclSETGOALS comb <*>
  Proofview.tclUNIT v
  }

let refine_one ?(unsafe = true) f =
  Proofview.Goal.enter_one (make_refine_enter ~unsafe f)

let refine ?(unsafe = true) f =
  let f = { run = fun sigma -> let Sigma (c,sigma,p) = f.run sigma in Sigma (((),c),sigma,p) } in
  Proofview.Goal.enter (make_refine_enter ~unsafe f)

(** Useful definitions *)

let with_type env evd c t =
  let my_type = Retyping.get_type_of env evd c in
  let my_type = EConstr.of_constr my_type in
  let j = Environ.make_judge c my_type in
  let (evd,j') =
    Coercion.inh_conv_coerce_to true (Loc.ghost) env evd j t
  in
  evd , j'.Environ.uj_val

let refine_casted ?unsafe f = Proofview.Goal.enter { enter = begin fun gl ->
  let gl = Proofview.Goal.assume gl in
  let concl = Proofview.Goal.concl gl in
  let concl = EConstr.of_constr concl in
  let env = Proofview.Goal.env gl in
  let f = { run = fun h ->
    let Sigma (c, h, p) = f.run h in
    let sigma, c = with_type env (Sigma.to_evar_map h) c concl in
    Sigma (c, Sigma.Unsafe.of_evar_map sigma, p)
  } in
  refine ?unsafe f
end }
