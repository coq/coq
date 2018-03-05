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
open Names
open Termops
open EConstr
open Inductiveops
open Hipattern
open Tacmach.New
open Tacticals.New
open Tactics
open Proofview.Notations

module NamedDecl = Context.Named.Declaration

(* Supposed to be called without as clause *)
let introElimAssumsThen tac ba =
  assert (ba.Tacticals.branchnames == []);
  let introElimAssums = tclDO ba.Tacticals.nassums intro in
  (tclTHEN introElimAssums (elim_on_ba tac ba))

(* Supposed to be called with a non-recursive scheme *)
let introCaseAssumsThen with_evars tac ba =
  let n1 = List.length ba.Tacticals.branchsign in
  let n2 = List.length ba.Tacticals.branchnames in
  let (l1,l2),l3 =
    if n1 < n2 then List.chop n1 ba.Tacticals.branchnames, []
    else (ba.Tacticals.branchnames, []), List.make (n1-n2) false in
  let introCaseAssums =
    tclTHEN (intro_patterns with_evars l1) (intros_clearing l3) in
  (tclTHEN introCaseAssums (case_on_ba (tac l2) ba))

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

let elimHypThen tac id =
  elimination_then tac (mkVar id)

let rec general_decompose_on_hyp recognizer =
  ifOnHyp recognizer (general_decompose_aux recognizer) (fun _ -> Proofview.tclUNIT())

and general_decompose_aux recognizer id =
  elimHypThen
    (introElimAssumsThen
       (fun bas ->
	  tclTHEN (clear [id])
	    (tclMAP (general_decompose_on_hyp recognizer)
               (ids_of_named_context bas.Tacticals.assums))))
    id

(* We should add a COMPLETE to be sure that the created hypothesis
   doesn't stay if no elimination is possible *)

(* Best strategies but loss of compatibility *)
let tmphyp_name = Id.of_string "_TmpHyp"
let up_to_delta = ref false (* true *)

let general_decompose recognizer c =
  Proofview.Goal.enter begin fun gl ->
  let type_of = pf_unsafe_type_of gl in
  let sigma = project gl in
  let typc = type_of c in
  tclTHENS (cut typc)
    [ tclTHEN (intro_using tmphyp_name)
         (onLastHypId
	    (ifOnHyp (recognizer sigma) (general_decompose_aux (recognizer sigma))
	      (fun id -> clear [id])));
       exact_no_check c ]
  end

let head_in indl t gl =
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  try
    let ity,_ =
      if !up_to_delta
      then find_mrectype env sigma t
      else extract_mrectype sigma t
    in List.exists (fun i -> eq_ind (fst i) (fst ity)) indl
  with Not_found -> false

let decompose_these c l =
  Proofview.Goal.enter begin fun gl ->
  let indl = List.map (fun x -> x, Univ.Instance.empty) l in
  general_decompose (fun sigma (_,t) -> head_in indl t gl) c
  end

let decompose_and c =
  general_decompose
    (fun sigma (_,t) -> is_record sigma t)
    c

let decompose_or c =
  general_decompose
    (fun sigma (_,t) -> is_disjunction sigma t)
    c

let h_decompose l c = decompose_these c l

let h_decompose_or = decompose_or

let h_decompose_and = decompose_and

(* The tactic Double performs a double induction *)

let simple_elimination c =
  elimination_then (fun _ -> tclIDTAC) c

let induction_trailer abs_i abs_j bargs =
  tclTHEN
    (tclDO (abs_j - abs_i) intro)
    (onLastHypId
       (fun id ->
          Proofview.Goal.enter begin fun gl ->
	  let idty = pf_unsafe_type_of gl (mkVar id) in
	  let fvty = global_vars (pf_env gl) (project gl) idty in
	  let possible_bring_hyps =
	    (List.tl (nLastDecls gl (abs_j - abs_i))) @ bargs.Tacticals.assums
          in
	  let (hyps,_) =
            List.fold_left
	      (fun (bring_ids,leave_ids) d ->
                 let cid = NamedDecl.get_id d in
                 if not (List.mem cid leave_ids)
                 then (d::bring_ids,leave_ids)
                 else (bring_ids,cid::leave_ids))
	      ([],fvty) possible_bring_hyps
	  in
          let ids = List.rev (ids_of_named_context hyps) in
	  (tclTHENLIST
            [revert ids; simple_elimination (mkVar id)])
          end
          ))

let double_ind h1 h2 =
  Proofview.Goal.enter begin fun gl ->
  let abs_i = depth_of_quantified_hypothesis true h1 gl in
  let abs_j = depth_of_quantified_hypothesis true h2 gl in
  let abs =
    if abs_i < abs_j then Proofview.tclUNIT (abs_i,abs_j) else
    if abs_i > abs_j then  Proofview.tclUNIT (abs_j,abs_i) else
      tclZEROMSG (Pp.str "Both hypotheses are the same.") in
  abs >>= fun (abs_i,abs_j) ->
  (tclTHEN (tclDO abs_i intro)
     (onLastHypId
       	(fun id ->
           elimination_then
             (introElimAssumsThen (induction_trailer abs_i abs_j)) (mkVar id))))
  end

let h_double_induction = double_ind


