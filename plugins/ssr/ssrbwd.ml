(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Printer
open Pretyping
open Glob_term

open Ssrmatching_plugin
open Ssrmatching

open Ssrast
open Ssrcommon

(** Backward chaining tactics: apply, exact, congr. *)

(** The "apply" tactic *)

let interp_agen ist env sigma ((goclr, _), (k, gc as c)) (clr, rcs) =
(* ppdebug(lazy(str"sigma@interp_agen=" ++ pr_evar_map None (project gl))); *)
  let rc = intern_term ist env c in
  let rcs' = rc :: rcs in
  match goclr with
  | None -> clr, rcs'
  | Some ghyps ->
    let clr' = interp_hyps ist env sigma ghyps @ clr in
    if k <> NoFlag then clr', rcs' else
    let loc = rc.CAst.loc in
    match DAst.get rc with
    | GVar id when not_section_id id -> SsrHyp (Loc.tag ?loc id) :: clr', rcs'
    | GRef (Names.GlobRef.VarRef id, _) when not_section_id id ->
        SsrHyp (Loc.tag ?loc id) :: clr', rcs'
    | _ -> clr', rcs'

let interp_nbargs ist env sigma rc =
  try
    let rc6 = mkRApp rc (mkRHoles 6) in
    let t = interp_open_constr env sigma ist (rc6, None) in
    6 + Ssrcommon.nbargs_open_constr env t
  with e when CErrors.noncritical e -> 5

let interp_view_nbimps ist env sigma rc =
  try
    let t = interp_open_constr env sigma ist (rc, None) in
    let pl, c = splay_open_constr env t in
    if Ssrcommon.isAppInd env sigma c then List.length pl else (-(List.length pl))
  with e when CErrors.noncritical e -> 0

let interp_agens ist env sigma ~concl gagens =
  match List.fold_right (interp_agen ist env sigma) gagens ([], []) with
  | clr, rlemma :: args ->
    let n = interp_nbargs ist env sigma rlemma - List.length args in
    let rec loop i =
      if i > n then
         errorstrm Pp.(str "Cannot apply lemma " ++ pr_glob_constr_env env sigma rlemma)
      else
        try interp_refine env sigma ist ~concl (mkRApp rlemma (mkRHoles i @ args))
        with e when CErrors.noncritical e -> loop (i + 1) in
    clr, loop 0
  | _ -> assert false

let apply_rconstr ?ist t =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let cl = Proofview.Goal.concl gl in
(* ppdebug(lazy(str"sigma@apply_rconstr=" ++ pr_evar_map None (project gl))); *)
  let n = match ist, DAst.get t with
    | None, (GVar id | GRef (Names.GlobRef.VarRef id,_)) -> pf_nbargs env sigma (EConstr.mkVar id)
    | Some ist, _ -> interp_nbargs ist env sigma t
    | _ -> anomaly "apply_rconstr without ist and not RVar" in
  let mkRlemma i = mkRApp t (mkRHoles i) in
  let rec loop i =
    if i > n then
      errorstrm Pp.(str"Cannot apply lemma "++pr_glob_constr_env env sigma t)
    else try understand_tcc env sigma ~expected_type:(OfType cl) (mkRlemma i)
      with e when CErrors.noncritical e -> loop (i + 1) in
  refine_with (loop 0)
  end

let mkRAppView ist env sigma rv gv =
  let nb_view_imps = interp_view_nbimps ist env sigma rv in
  mkRApp rv (mkRHoles (abs nb_view_imps))

let refine_interp_apply_view dbl ist gv =
  let open Tacmach in
  Proofview.Goal.enter begin fun gl ->
  let pair i = List.map (fun x -> i, x) in
  let rv = intern_term ist (pf_env gl) gv in
  let v = mkRAppView ist (pf_env gl) (project gl) rv gv in
  let interp_with (dbl, hint) =
    let i = if dbl = Ssrview.AdaptorDb.Equivalence then 2 else 1 in
    interp_refine (pf_env gl) (project gl) ist ~concl:(pf_concl gl) (mkRApp hint (v :: mkRHoles i)) in
  let rec loop = function
  | [] -> Proofview.tclORELSE (apply_rconstr ~ist rv) (fun _ -> view_error "apply" gv)
  | h :: hs ->
    match interp_with h with
    | t -> Proofview.tclORELSE (refine_with t) (fun _ -> loop hs)
    | exception e when CErrors.noncritical e -> loop hs
  in
  loop (pair dbl (Ssrview.AdaptorDb.get dbl) @
        if dbl = Ssrview.AdaptorDb.Equivalence
        then pair Ssrview.AdaptorDb.Backward (Ssrview.AdaptorDb.(get Backward))
        else [])
  end

let apply_top_tac =
  Proofview.Goal.enter begin fun _ ->
  Tacticals.tclTHENLIST [
    introid top_id;
    apply_rconstr (mkRVar top_id);
    cleartac [SsrHyp(None,top_id)]
  ]
  end

let inner_ssrapplytac gviews (ggenl, gclr) ist =
  let open Tacmach in
  Proofview.Goal.enter begin fun gl ->

 let clr = interp_hyps ist (pf_env gl) (project gl) gclr in
 let vtac gv i = refine_interp_apply_view i ist gv in
 let ggenl, tclGENTAC =
   if gviews <> [] && ggenl <> [] then
     let ggenl= List.map (fun (x,(k,p)) -> x, {kind=k; pattern=p; interpretation= Some ist}) (List.hd ggenl) in
     [], Tacticals.tclTHEN (genstac (ggenl,[]))
   else ggenl, (fun tac -> tac) in
 tclGENTAC (Proofview.Goal.enter (fun gl ->
 let open Tacmach in
  match gviews, ggenl with
  | v :: tl, [] ->
    let dbl =
      if List.length tl = 1
      then Ssrview.AdaptorDb.Equivalence
      else Ssrview.AdaptorDb.Backward in
    Tacticals.tclTHEN
      (List.fold_left (fun acc v ->
         Tacticals.tclTHENLAST acc (vtac v dbl))
        (vtac v Ssrview.AdaptorDb.Backward) tl)
      (cleartac clr)
  | [], [agens] ->
    let sigma = Proofview.Goal.sigma gl in
    let clr', lemma = interp_agens ist (pf_env gl) sigma ~concl:(pf_concl gl) agens in
    let sigma = Evd.merge_universe_context sigma (Evd.ustate (fst lemma)) in
    Tacticals.tclTHENLIST [Proofview.Unsafe.tclEVARS sigma; cleartac clr; refine_with ~beta:true lemma; cleartac clr']
  | _, _ ->
    Tacticals.tclTHENLIST [apply_top_tac; cleartac clr]))

  end
