(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Termops
open EConstr
open Inductiveops
open Hipattern
open Tacmach
open Tacticals
open Tactics

type elim_kind = Case of bool | Elim

(* Find the right elimination suffix corresponding to the sort of the goal *)
(* c should be of type A1->.. An->B with B an inductive definition *)
let general_elim_using mk_elim (ind, u, args) id = match mk_elim with
| Case dep ->
  Clenv.case_pf ~dep (mkVar id, mkApp (mkIndU (ind, u), args))
| Elim ->
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let sort = Retyping.get_sort_family_of env sigma (Proofview.Goal.concl gl) in
    let flags = Unification.elim_flags () in
    let gr = Indrec.lookup_eliminator env ind sort in
    let sigma, elim = Evd.fresh_global env sigma gr in
    let elimt = Retyping.get_type_of env sigma elim in
    (* applying elimination_scheme just a little modified *)
    let elimclause = Clenv.mk_clenv_from env sigma (elim, elimt) in
    let indmv = List.last (Clenv.clenv_arguments elimclause) in
    let elimclause = Clenv.clenv_instantiate indmv elimclause (mkVar id, mkApp (mkIndU (ind, u), args)) in
    Clenv.res_pf ~flags elimclause
  end

(* computing the case/elim combinators *)

let elim_on_ba tac nassums =
  Proofview.Goal.enter begin fun gl ->
  let branches =
    try List.rev (List.firstn nassums (Proofview.Goal.hyps gl))
    with Failure _ -> CErrors.anomaly (Pp.str "make_elim_branch_assumptions.")
  in
  tac branches
  end

let case_tac dep names tac (ind, u, args as spec) c =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let branchsigns = Tacticals.compute_constructor_signatures env ~rec_flag:false (ind, u) in
    let brnames = Tacticals.compute_induction_names false branchsigns names in
    let after_tac i =
      let branchnames = brnames.(i) in
      let n1 = List.length branchsigns.(i) in
      let n2 = List.length branchnames in
      let (l1,l2),l3 =
        if n1 < n2 then List.chop n1 branchnames, []
        else (branchnames, []), List.make (n1-n2) false in
      (intro_patterns false l1) <*> (intros_clearing l3) <*> (elim_on_ba (tac l2) n1)
    in
    let branchtacs = List.init (Array.length branchsigns) after_tac in
    general_elim_using (Case dep) spec c <*>
    (Proofview.tclEXTEND [] tclIDTAC branchtacs)
  end

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

let rec general_decompose_aux recognizer id =
  let open Declarations in
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let ((ind, u), t) = pf_apply Tacred.reduce_to_atomic_ind gl (pf_get_type_of gl (mkVar id)) in
  let _, args = decompose_app (Proofview.Goal.sigma gl) t in
  let rec_flag, mkelim =
    match (Environ.lookup_mind (fst ind) env).mind_record with
    | NotRecord -> true, Elim
    | FakeRecord | PrimRecord _ -> false, Case true
  in
  let branchsigns = Tacticals.compute_constructor_signatures env ~rec_flag (ind, u) in
  let next_tac bas =
    let map id = ifOnHyp recognizer (general_decompose_aux recognizer) (fun _ -> tclIDTAC) id in
    tclMAP map (ids_of_named_context bas)
  in
  let after_tac i =
    let nassums = List.length branchsigns.(i) in
    (tclDO nassums intro) <*> (clear [id]) <*> (elim_on_ba next_tac nassums)
  in
  let branchtacs = List.init (Array.length branchsigns) after_tac in
  general_elim_using mkelim (ind, u, args) id <*>
  (Proofview.tclEXTEND [] tclIDTAC branchtacs)
  end


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
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  try
    let ity,_ = extract_mrectype sigma t in
    List.exists (fun i -> Environ.QInd.equal env (fst i) (fst ity)) indl
  with Not_found -> false

let decompose_these c l =
  Proofview.Goal.enter begin fun gl ->
  let indl = List.map (fun x -> x, UVars.Instance.empty) l in
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
