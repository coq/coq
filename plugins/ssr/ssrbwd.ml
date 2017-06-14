(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Printer
open Pretyping
open Globnames
open Glob_term
open Tacmach

open Ssrmatching_plugin
open Ssrmatching

open Ssrast
open Ssrprinters
open Ssrcommon

let char_to_kind = function
  | '(' -> xInParens
  | '@' -> xWithAt
  | ' ' -> xNoFlag
  | 'x' -> xCpattern
  | _ -> assert false

(** Backward chaining tactics: apply, exact, congr. *)

(** The "apply" tactic *)

let interp_agen ist gl ((goclr, _), (k, gc as c)) (clr, rcs) =
(* ppdebug(lazy(str"sigma@interp_agen=" ++ pr_evar_map None (project gl))); *)
  let k = char_to_kind k in
  let rc = pf_intern_term ist gl c in
  let rcs' = rc :: rcs in
  match goclr with
  | None -> clr, rcs'
  | Some ghyps ->
    let clr' = snd (interp_hyps ist gl ghyps) @ clr in
    if k <> xNoFlag then clr', rcs' else
    let open CAst in
    match rc with
    | { loc; v = GVar id } when not_section_id id -> SsrHyp (Loc.tag ?loc id) :: clr', rcs'
    | { loc; v = GRef (VarRef id, _) } when not_section_id id ->
        SsrHyp (Loc.tag ?loc id) :: clr', rcs'
    | _ -> clr', rcs'

let pf_pr_glob_constr gl = pr_glob_constr_env (pf_env gl)

let interp_agens ist gl gagens =
  match List.fold_right (interp_agen ist gl) gagens ([], []) with
  | clr, rlemma :: args ->
    let n = interp_nbargs ist gl rlemma - List.length args in
    let rec loop i =
      if i > n then
         errorstrm Pp.(str "Cannot apply lemma " ++ pf_pr_glob_constr gl rlemma)
      else
        try interp_refine ist gl (mkRApp rlemma (mkRHoles i @ args))
        with _ -> loop (i + 1) in
    clr, loop 0
  | _ -> assert false

let pf_match = pf_apply (fun e s c t -> understand_tcc e s ~expected_type:t c)

let apply_rconstr ?ist t gl =
(* ppdebug(lazy(str"sigma@apply_rconstr=" ++ pr_evar_map None (project gl))); *)
  let open CAst in
  let n = match ist, t with
    | None, { v = GVar id | GRef (VarRef id,_) } -> pf_nbargs gl (EConstr.mkVar id)
    | Some ist, _ -> interp_nbargs ist gl t
    | _ -> anomaly "apply_rconstr without ist and not RVar" in
  let mkRlemma i = mkRApp t (mkRHoles i) in
  let cl = pf_concl gl in
  let rec loop i =
    if i > n then
      errorstrm Pp.(str"Cannot apply lemma "++pf_pr_glob_constr gl t)
    else try pf_match gl (mkRlemma i) (OfType cl) with _ -> loop (i + 1) in
  refine_with (loop 0) gl

let mkRAppView ist gl rv gv =
  let nb_view_imps = interp_view_nbimps ist gl rv in
  mkRApp rv (mkRHoles (abs nb_view_imps))

let prof_apply_interp_with = mk_profiler "ssrapplytac.interp_with";;

let refine_interp_apply_view i ist gl gv =
  let pair i = List.map (fun x -> i, x) in
  let rv = pf_intern_term ist gl gv in
  let v = mkRAppView ist gl rv gv in
  let interp_with (i, hint) =
    interp_refine ist gl (mkRApp hint (v :: mkRHoles i)) in
  let interp_with x = prof_apply_interp_with.profile interp_with x in
  let rec loop = function
  | [] -> (try apply_rconstr ~ist rv gl with _ -> view_error "apply" gv)
  | h :: hs -> (try refine_with (snd (interp_with h)) gl with _ -> loop hs) in
  loop (pair i Ssrview.viewtab.(i) @
        if i = 2 then pair 1 Ssrview.viewtab.(1) else [])

let apply_top_tac gl =
  Tacticals.tclTHENLIST [introid top_id; apply_rconstr (mkRVar top_id); Proofview.V82.of_tactic (Tactics.clear [top_id])] gl

let inner_ssrapplytac gviews ggenl gclr ist gl =
 let _, clr = interp_hyps ist gl gclr in
 let vtac gv i gl' = refine_interp_apply_view i ist gl' gv in
 let ggenl, tclGENTAC =
   if gviews <> [] && ggenl <> [] then
     let ggenl= List.map (fun (x,g) -> x, cpattern_of_term g) (List.hd ggenl) in
     [], Tacticals.tclTHEN (genstac (ggenl,[]) ist)
   else ggenl, Tacticals.tclTHEN Tacticals.tclIDTAC in
 tclGENTAC (fun gl ->
  match gviews, ggenl with
  | v :: tl, [] ->
    let dbl = if List.length tl = 1 then 2 else 1 in
    Tacticals.tclTHEN
      (List.fold_left (fun acc v -> Tacticals.tclTHENLAST acc (vtac v dbl)) (vtac v 1) tl)
      (cleartac clr) gl
  | [], [agens] ->
    let clr', (sigma, lemma) = interp_agens ist gl agens in
    let gl = pf_merge_uc_of sigma gl in
    Tacticals.tclTHENLIST [cleartac clr; refine_with ~beta:true lemma; cleartac clr'] gl
  | _, _ -> Tacticals.tclTHEN apply_top_tac (cleartac clr) gl) gl

