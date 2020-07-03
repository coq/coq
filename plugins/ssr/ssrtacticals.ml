(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Names
open Constr
open Context
open Termops
open Tacmach

open Ssrast
open Ssrcommon

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(** Tacticals (+, -, *, done, by, do, =>, first, and last). *)

let get_index = function Locus.ArgArg i -> i | _ ->
  anomaly "Uninterpreted index"
(* Toplevel constr must be globalized twice ! *)

(** The "first" and "last" tacticals. *)

let tclPERM perm tac =
  Proofview.V82.tactic begin fun gls ->
  let subgls = Proofview.V82.of_tactic tac gls in
  let subgll' = perm subgls.Evd.it in
  re_sig subgll' subgls.Evd.sigma
  end

let rot_hyps dir i hyps =
  let n = List.length hyps in
  if i = 0 then List.rev hyps else
  if i > n then CErrors.user_err (Pp.str "Not enough subgoals") else
  let rec rot i l_hyps = function
    | hyp :: hyps' when i > 0 -> rot (i - 1) (hyp :: l_hyps) hyps'
    | hyps' -> hyps' @ (List.rev l_hyps) in
  rot (match dir with L2R -> i | R2L -> n - i) [] hyps

let tclSEQAT ist atac1 dir (ivar, ((_, atacs2), atac3)) =
  let i = get_index ivar in
  let evtac t = ssrevaltac ist t in
  let tac1 = evtac atac1 in
  if atacs2 = [] && atac3 <> None then tclPERM (rot_hyps dir i) tac1  else
  let evotac = function Some atac -> evtac atac | _ -> Tacticals.New.tclIDTAC in
  let tac3 = evotac atac3 in
  let rec mk_pad n = if n > 0 then tac3 :: mk_pad (n - 1) else [] in
  match dir, mk_pad (i - 1), List.map evotac atacs2 with
  | L2R, [], [tac2] when atac3 = None -> Tacticals.New.tclTHENFIRST tac1 tac2
  | L2R, [], [tac2] when atac3 = None -> Tacticals.New.tclTHENLAST tac1 tac2
  | L2R, pad, tacs2 -> Tacticals.New.tclTHENSFIRSTn tac1 (Array.of_list (pad @ tacs2)) tac3
  | R2L, pad, tacs2 -> Tacticals.New.tclTHENSLASTn tac1 tac3 (Array.of_list (tacs2 @ pad))

(** The "in" pseudo-tactical *)(* {{{ **********************************************)

let hidden_goal_tag = "the_hidden_goal"

let check_wgen_uniq gens =
  let clears = List.flatten (List.map fst gens) in
  check_hyps_uniq [] clears;
  let ids = CList.map_filter
    (function (_,Some ((id,_),_)) -> Some (hoi_id id) | _ -> None) gens in
  let rec check ids = function
  | id :: _ when List.mem id ids ->
    errorstrm Pp.(str"Duplicate generalization " ++ Id.print id)
  | id :: hyps -> check (id :: ids) hyps
  | [] -> () in
  check [] ids

let pf_clauseids gens clseq =
  let keep_clears = List.map (fun (x, _) -> x, None) in
  if gens <> [] then (check_wgen_uniq gens; gens) else
  if clseq <> InAll && clseq <> InAllHyps then keep_clears gens else
  CErrors.user_err (Pp.str "assumptions should be named explicitly")

let hidden_clseq = function InHyps | InHypsSeq | InAllHyps -> true | _ -> false

let posetac id cl = Tactics.pose_tac (Name id) cl

let hidetacs clseq idhide cl0 =
  if not (hidden_clseq clseq) then  [] else
  [posetac idhide cl0;
   convert_concl_no_check (EConstr.mkVar idhide)]

let endclausestac id_map clseq gl_id cl0 =
  Proofview.V82.tactic begin fun gl ->
  let not_hyp' id = not (List.mem_assoc id id_map) in
  let orig_id id = try List.assoc id id_map with Not_found -> id in
  let dc, c = EConstr.decompose_prod_assum (project gl) (pf_concl gl) in
  let hide_goal = hidden_clseq clseq in
  let c_hidden =
    hide_goal && EConstr.eq_constr (project gl) c (EConstr.mkVar gl_id) in
  let rec fits forced = function
  | (id, _) :: ids, decl :: dc' when RelDecl.get_name decl = Name id ->
    fits true (ids, dc')
  | ids, dc' ->
    forced && ids = [] && (not hide_goal || dc' = [] && c_hidden) in
  let rec unmark c = match EConstr.kind (project gl) c with
  | Var (id, _) when hidden_clseq clseq && id = gl_id -> cl0
  | Prod ({binder_name=Name id} as na, t, c') when List.mem_assoc id id_map ->
    EConstr.mkProd ({na with binder_name=Name (orig_id id)}, unmark t, unmark c')
  | LetIn ({binder_name=Name id} as na, v, t, c') when List.mem_assoc id id_map ->
    EConstr.mkLetIn ({na with binder_name=Name (orig_id id)}, unmark v, unmark t, unmark c')
  | _ -> EConstr.map (project gl) unmark c in
  let utac hyp =
    Proofview.V82.of_tactic
     (Tactics.convert_hyp ~check:false ~reorder:false (NamedDecl.map_constr unmark hyp)) in
  let utacs = List.map utac (pf_hyps gl) in
  let ugtac gl' =
    Proofview.V82.of_tactic
      (convert_concl_no_check (unmark (pf_concl gl'))) gl' in
  let ctacs =
    if hide_goal then [Proofview.V82.of_tactic (Tactics.clear [gl_id])]
    else [] in
  let mktac itacs = Tacticals.tclTHENLIST (itacs @ utacs @ ugtac :: ctacs) in
  let itac (_, id) = Proofview.V82.of_tactic (Tactics.introduction id) in
  if fits false (id_map, List.rev dc) then mktac (List.map itac id_map) gl else
  let all_ids = ids_of_rel_context dc @ pf_ids_of_hyps gl in
  if List.for_all not_hyp' all_ids && not c_hidden then mktac [] gl else
  errorstrm Pp.(str "tampering with discharged assumptions of \"in\" tactical")
  end

let tclCLAUSES tac (gens, clseq) =
  Proofview.Goal.enter begin fun gl ->
  if clseq = InGoal || clseq = InSeqGoal then tac else
  let clr_gens = pf_clauseids gens clseq in
  let clear = Tacticals.New.tclTHENLIST (List.rev(List.fold_right clr_of_wgen clr_gens [])) in
  let gl_id = mk_anon_id hidden_goal_tag (Tacmach.New.pf_ids_of_hyps gl) in
  let cl0 = Proofview.Goal.concl gl in
  let dtac =
    Proofview.V82.tactic begin fun gl ->
    let c = pf_concl gl in
    let gl, args, c =
      List.fold_right (abs_wgen true mk_discharged_id) gens (gl,[], c) in
    apply_type c args gl
    end
  in
  let endtac =
    let id_map = CList.map_filter (function
      | _, Some ((x,_),_) -> let id = hoi_id x in Some (mk_discharged_id id, id)
      | _, None -> None) gens in
    endclausestac id_map clseq gl_id cl0 in
  Tacticals.New.tclTHENLIST (hidetacs clseq gl_id cl0 @ [dtac; clear; tac; endtac])
  end

(** The "do" tactical. ********************************************************)

let hinttac ist is_by (is_or, atacs) =
  Proofview.Goal.enter begin fun _ ->
  let dtac = if is_by then donetac ~-1 else Tacticals.New.tclIDTAC in
  let mktac = function
  | Some atac -> Tacticals.New.tclTHEN (ssrevaltac ist atac) dtac
  | _ -> dtac in
  match List.map mktac atacs with
  | [] -> if is_or then dtac else Tacticals.New.tclIDTAC
  | [tac] -> tac
  | tacs -> Tacticals.New.tclFIRST tacs
  end

let ssrdotac ist (((n, m), tac), clauses) =
  let mul = get_index n, m in
  tclCLAUSES (tclMULT mul (hinttac ist false tac)) clauses
