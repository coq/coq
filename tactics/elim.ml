(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open Termops
open EConstr
open Inductiveops
open Hipattern
open Tacmach
open Tacticals
open Clenv
open Tactics

type branch_args = {
  branchnum  : int;         (* the branch number *)
  nassums    : int;         (* number of assumptions/letin to be introduced *)
  branchsign : bool list;   (* the signature of the branch.
                               true=assumption, false=let-in *)
  branchnames : Tactypes.intro_patterns}

type elim_kind = Case of bool | Elim

(* Find the right elimination suffix corresponding to the sort of the goal *)
(* c should be of type A1->.. An->B with B an inductive definition *)
let general_elim_then_using mk_elim
    rec_flag allnames tac predicate (ind, u, args) id =
  let open Pp in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let sort = Retyping.get_sort_family_of env sigma (Proofview.Goal.concl gl) in
    let sigma, elim, elimt = match mk_elim with
    | Case dep ->
      let u = EInstance.kind sigma u in
      let (sigma, r, t) = Indrec.build_case_analysis_scheme env sigma (ind, u) dep sort in
      (sigma, EConstr.of_constr r, EConstr.of_constr t)
    | Elim ->
      let gr = Indrec.lookup_eliminator env ind sort in
      let sigma, r = Evd.fresh_global env sigma gr in
      (sigma, r, Retyping.get_type_of env sigma r)
    in
    (* applying elimination_scheme just a little modified *)
    let elimclause = mk_clenv_from env sigma (elim, elimt) in
    let indmv =
      match EConstr.kind elimclause.evd (last_arg elimclause.evd elimclause.templval.Evd.rebus) with
      | Meta mv -> mv
      | _         -> CErrors.anomaly (str"elimination.")
    in
    let pmv =
      let p, _ = decompose_app elimclause.evd elimclause.templtyp.Evd.rebus in
      match EConstr.kind elimclause.evd p with
      | Meta p -> p
      | _ ->
          let name_elim =
            match EConstr.kind sigma elim with
            | Const _ | Var _ -> str " " ++ Printer.pr_econstr_env env sigma elim
            | _ -> mt ()
          in
          CErrors.user_err
            (str "The elimination combinator " ++ name_elim ++ str " is unknown.")
    in
    let elimclause' = clenv_instantiate indmv elimclause (mkVar id, mkApp (mkIndU (ind, u), args)) in
    let branchsigns = Tacticals.compute_constructor_signatures env ~rec_flag (ind, u) in
    let brnames = Tacticals.compute_induction_names false branchsigns allnames in
    let flags = Unification.elim_flags () in
    let elimclause' =
      match predicate with
      | None   -> elimclause'
      | Some p -> clenv_unify ~flags Reduction.CONV (mkMeta pmv) p elimclause'
    in
    let after_tac i =
      let ba = { branchsign = branchsigns.(i);
                  branchnames = brnames.(i);
                  nassums = List.length branchsigns.(i);
                  branchnum = i+1; }
      in
      tac ba
    in
    let branchtacs = List.init (Array.length branchsigns) after_tac in
    Proofview.tclTHEN
      (Clenv.res_pf ~flags elimclause')
      (Proofview.tclEXTEND [] tclIDTAC branchtacs)
  end

(* computing the case/elim combinators *)

let make_elim_branch_assumptions ba hyps =
  let assums =
    try List.rev (List.firstn ba.nassums hyps)
    with Failure _ -> CErrors.anomaly (Pp.str "make_elim_branch_assumptions.") in
  assums

let elim_on_ba tac ba =
  Proofview.Goal.enter begin fun gl ->
  let branches = make_elim_branch_assumptions ba (Proofview.Goal.hyps gl) in
  tac branches
  end

let elimination_then tac id =
  let open Declarations in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let ((ind, u), t) = pf_apply Tacred.reduce_to_atomic_ind gl (pf_get_type_of gl (mkVar id)) in
  let _, args = decompose_app_vect (Proofview.Goal.sigma gl) t in
  let isrec,mkelim =
    match (Environ.lookup_mind (fst ind) env).mind_record with
    | NotRecord -> true, Elim
    | FakeRecord | PrimRecord _ -> false, Case true
  in
  general_elim_then_using mkelim isrec None tac None (ind, u, args) id
  end

(* Supposed to be called without as clause *)
let introElimAssumsThen tac ba =
  assert (ba.branchnames == []);
  let introElimAssums = tclDO ba.nassums intro in
  (tclTHEN introElimAssums (elim_on_ba tac ba))

(* Supposed to be called with a non-recursive scheme *)
let introCaseAssumsThen with_evars tac ba =
  let n1 = List.length ba.branchsign in
  let n2 = List.length ba.branchnames in
  let (l1,l2),l3 =
    if n1 < n2 then List.chop n1 ba.branchnames, []
    else (ba.branchnames, []), List.make (n1-n2) false in
  let introCaseAssums =
    tclTHEN (intro_patterns with_evars l1) (intros_clearing l3) in
  (tclTHEN introCaseAssums (elim_on_ba (tac l2) ba))

let case_tac dep names tac elim ind c =
  let tac = introCaseAssumsThen false (* ApplyOn not supported by inversion *) tac in
  general_elim_then_using (Case dep) false names tac (Some elim) ind c

(* The following tactic Decompose repeatedly applies the
   elimination(s) rule(s) of the types satisfying the predicate
   ``recognizer'' onto a certain hypothesis. For example :

Require Elim.
Require Le.
   Goal (y:nat){x:nat | (le O x)/\(le x y)}->{x:nat | (le O x)}.
   Intros y H.
   Decompose [sig and] H;EAuto.
   Qed.

Another example :

   Goal (A,B,C:Prop)(A/\B/\C \/ B/\C \/ C/\A) -> C.
   Intros A B C H; Decompose [and or] H; Assumption.
   Qed.
*)

let rec general_decompose_on_hyp recognizer =
  ifOnHyp recognizer (general_decompose_aux recognizer) (fun _ -> Proofview.tclUNIT())

and general_decompose_aux recognizer id =
  elimination_then
    (introElimAssumsThen
       (fun bas ->
          tclTHEN (clear [id])
            (tclMAP (general_decompose_on_hyp recognizer)
               (ids_of_named_context bas))))
    id

(* We should add a COMPLETE to be sure that the created hypothesis
   doesn't stay if no elimination is possible *)

(* Best strategies but loss of compatibility *)
let tmphyp_name = Id.of_string "_TmpHyp"

let general_decompose recognizer c =
  Proofview.Goal.enter begin fun gl ->
  let typc = pf_get_type_of gl c in
  tclTHENS (cut typc)
    [ intro_using_then tmphyp_name (fun id ->
          ifOnHyp recognizer (general_decompose_aux recognizer)
            (fun id -> clear [id])
            id);
       exact_no_check c ]
  end

let head_in indl t gl =
  let sigma = Tacmach.project gl in
  try
    let ity,_ = extract_mrectype sigma t in
    List.exists (fun i -> Ind.CanOrd.equal (fst i) (fst ity)) indl
  with Not_found -> false

let decompose_these c l =
  Proofview.Goal.enter begin fun gl ->
  let indl = List.map (fun x -> x, Univ.Instance.empty) l in
  general_decompose (fun env sigma (_,t) -> head_in indl t gl) c
  end

let decompose_and c =
  general_decompose
    (fun env sigma (_,t) -> is_record env sigma t)
    c

let decompose_or c =
  general_decompose
    (fun env sigma (_,t) -> is_disjunction env sigma t)
    c

let h_decompose l c = decompose_these c l

let h_decompose_or = decompose_or

let h_decompose_and = decompose_and
