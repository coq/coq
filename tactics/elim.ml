(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Term
open Termops
open Environ
open Libnames
open Reduction
open Inductiveops
open Clenv
open Hipattern
open Tacticals
open Tactics
open Hiddentac
open Genarg
open Tacexpr

(* arnaud: trucs factices *)
let pf_type_of _ = Util.anomaly "Elim.pf_type_of: fantome"
let pf_env _ = Util.anomaly "Elim.pf_env: fantome"
let project _ = Util.anomaly "Elim.project: fantome"
module Refiner =
  struct
    let abstract_tactic _ = Util.anomaly "Elim.Refiner.abstract_tactic: fantome"
  end 
(* arnaud: /trucs factices *)

let introElimAssumsThen tac ba =
  let nassums = 
    List.fold_left 
      (fun acc b -> if b then acc+2 else acc+1) 
      0 ba.branchsign 
  in 
  let introElimAssums = tclDO nassums intro in 
  (tclTHEN introElimAssums (elim_on_ba tac ba))

let introCaseAssumsThen tac ba =
  let case_thin_sign =
    List.flatten
      (List.map (function b -> if b then [false;true] else [false])
	ba.branchsign)
  in 
  let n1 = List.length case_thin_sign in
  let n2 = List.length ba.branchnames in
  let (l1,l2),l3 =
    if n1 < n2 then list_chop n1 ba.branchnames, []
    else 
      (ba.branchnames, []),
       if n1 > n2 then snd (list_chop n2 case_thin_sign) else [] in
  let introCaseAssums = tclTHEN (intros_pattern None l1) (intros_clearing l3)
  in
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

let elimHypThen tac id gl =
  elimination_then tac ([],[]) (mkVar id) gl

let rec general_decompose_on_hyp recognizer =
  ifOnHyp recognizer (general_decompose recognizer) (fun _ -> tclIDTAC)

and general_decompose recognizer id =
  elimHypThen
    (introElimAssumsThen
       (fun bas ->
	  tclTHEN (clear [id])
	    (tclMAP (general_decompose_on_hyp recognizer)
               (ids_of_named_context bas.assums))))
    id

(* Faudrait ajouter un COMPLETE pour que l'hypothèse créée ne reste
   pas si aucune élimination n'est possible *)

(* Meilleures stratégies mais perte de compatibilité *)
let tmphyp_name = id_of_string "_TmpHyp"
let up_to_delta = ref false (* true *)

let general_decompose recognizer c gl = 
  let typc = pf_type_of gl c in  
  tclTHENSV (cut typc) 
    [| tclTHEN (intro_using tmphyp_name)
         (onLastHyp
	    (ifOnHyp recognizer (general_decompose recognizer)
	      (fun id -> clear [id])));
       exact_no_check c |] gl

let head_in gls indl t =
  try
    let ity,_ =
      if !up_to_delta
      then find_mrectype (pf_env gls) (project gls) t
      else extract_mrectype t
    in List.mem ity indl
  with Not_found -> false
       
let inductive_of = function
  | IndRef ity -> ity
  | r ->
      errorlabstrm "Decompose"
        (Printer.pr_global r ++ str " is not an inductive type")

let decompose_these c l gls =
  let indl = (*List.map inductive_of*) l in 
  general_decompose (fun (_,t) -> head_in gls indl t) c gls

let decompose_nonrec c gls =
  general_decompose 
    (fun (_,t) -> is_non_recursive_type t)
    c gls

let decompose_and c gls = 
  general_decompose 
    (fun (_,t) -> is_conjunction t)
    c gls

let decompose_or c gls = 
  general_decompose 
    (fun (_,t) -> is_disjunction t)
    c gls

let inj_open c = (Evd.empty,c)

let h_decompose l c =
  Refiner.abstract_tactic (TacDecompose (l,inj_open c)) (decompose_these c l)

let h_decompose_or c =
  Refiner.abstract_tactic (TacDecomposeOr (inj_open c)) (decompose_or c)

let h_decompose_and c =
  Refiner.abstract_tactic (TacDecomposeAnd (inj_open c)) (decompose_and c)

(* The tactic Double performs a double induction *)

let simple_elimination c gls =
  simple_elimination_then (fun _ -> tclIDTAC) c gls

let induction_trailer abs_i abs_j bargs =
  tclTHEN 
    (tclDO (abs_j - abs_i) intro)
    (onLastHyp
       (fun id gls ->
	  let idty = pf_type_of gls (mkVar id) in
	  let fvty = global_vars (pf_env gls) idty in
	  let possible_bring_hyps =
	    (List.tl (nLastHyps (abs_j - abs_i) gls)) @ bargs.assums
          in
	  let (hyps,_) =
            List.fold_left 
	      (fun (bring_ids,leave_ids) (cid,_,cidty as d) ->
                 if not (List.mem cid leave_ids)
                 then (d::bring_ids,leave_ids)
                 else (bring_ids,cid::leave_ids))
	      ([],fvty) possible_bring_hyps
	  in
          let ids = List.rev (ids_of_named_context hyps) in
	  (tclTHENSEQ
            [bring_hyps hyps; tclTRY (clear ids); 
	     simple_elimination (mkVar id)])
          gls))

let double_ind h1 h2 gls =
  let abs_i = depth_of_quantified_hypothesis true h1 gls in
  let abs_j = depth_of_quantified_hypothesis true h2 gls in
  let (abs_i,abs_j) =
    if abs_i < abs_j then (abs_i,abs_j) else
    if abs_i > abs_j then (abs_j,abs_i) else
      error "Both hypotheses are the same" in
  (tclTHEN (tclDO abs_i intro)
     (onLastHyp
       	(fun id ->
           elimination_then
             (introElimAssumsThen (induction_trailer abs_i abs_j))
             ([],[]) (mkVar id)))) gls

let h_double_induction h1 h2 =
  Refiner.abstract_tactic (TacDoubleInduction (h1,h2)) (double_ind h1 h2)


