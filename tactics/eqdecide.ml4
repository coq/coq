(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(*                              EqDecide                               *)
(*   A tactic for deciding propositional equality on inductive types   *)
(*                           by Eduardo Gimenez                        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Util
open Names
open Nameops
open Term
open Declarations
open Tactics
open Tacticals
open Hiddentac
open Equality
open Auto
open Pattern
open Matching
open Hipattern
open Proof_trees
open Proof_type
open Tacmach
open Coqlib

(* This file containts the implementation of the tactics ``Decide
   Equality'' and ``Compare''. They can be used to decide the
   propositional equality of two objects that belongs to a small
   inductive datatype --i.e., an inductive set such that all the
   arguments of its constructors are non-functional sets.

   The procedure for proving (x,y:R){x=y}+{~x=y} can be scketched as
   follows:
   1. Eliminate x and then y.
   2. Try discrimination to solve those goals where x and y has
      been introduced by different constructors.
   3. If x and y have been introduced by the same constructor,
      then analyse one by one the correspoing pairs of arguments.
      If they are equal, rewrite one into the other. If they are
      not, derive a contradiction from the injectiveness of the
      constructor. 
   4. Once all the arguments have been rewritten, solve the left half 
      of the disjunction by reflexivity.

   Eduardo Gimenez (30/3/98).
*)

let clear_last = (tclLAST_HYP (fun c -> (clear [destVar c])))

let mkBranches = 
  tclTHENSEQ
    [intro; 
     tclLAST_HYP h_simplest_elim;
     clear_last;
     intros ;
     tclLAST_HYP h_simplest_case;
     clear_last;
     intros]

let solveRightBranch  = 
  tclTHEN h_simplest_right
    (tclTHEN (intro_force true)
      (onLastHyp (fun id -> Extratactics.h_discrHyp (Rawterm.NamedHyp id))))

let h_solveRightBranch =
  Refiner.abstract_extended_tactic "solveRightBranch" [] solveRightBranch

(*
let h_solveRightBranch =
  hide_atomic_tactic "solveRightBranch" solveRightBranch
*)

(* Constructs the type {c1=c2}+{~c1=c2} *)

let mkDecideEqGoal rectype c1 c2 g = 
  let equality    = mkApp(build_coq_eq(), [|rectype; c1; c2|]) in
  let disequality = mkApp(build_coq_not (), [|equality|]) in
  mkApp(build_coq_sumbool (), [|equality; disequality |])


(* Constructs the type (x1,x2:R){x1=x2}+{~x1=x2} *)

let mkGenDecideEqGoal rectype g = 
  let hypnames = pf_ids_of_hyps g in 
  let xname    = next_ident_away (id_of_string "x") hypnames
  and yname    = next_ident_away (id_of_string "y") hypnames in
  (mkNamedProd xname rectype 
     (mkNamedProd yname rectype 
        (mkDecideEqGoal rectype (mkVar xname) (mkVar yname) g)))

let eqCase  tac = 
  (tclTHEN intro  
  (tclTHEN (tclLAST_HYP Extratactics.h_rewriteLR)
  (tclTHEN clear_last 
  tac)))

let diseqCase = 
  let diseq  = id_of_string "diseq" in
  let absurd = id_of_string "absurd" in 
  (tclTHEN (intro_using diseq)
  (tclTHEN  h_simplest_right
  (tclTHEN  red_in_concl
  (tclTHEN  (intro_using absurd)
  (tclTHEN  (h_simplest_apply (mkVar diseq))
  (tclTHEN  (Extratactics.h_injHyp (Rawterm.NamedHyp absurd))
            full_trivial))))))

let solveArg a1 a2 tac  g = 
  let rectype = pf_type_of g a1 in
  let decide  = mkDecideEqGoal rectype a1 a2 g in  
  (tclTHENS
     (h_elim_type decide) 
     [(eqCase tac);diseqCase;default_auto]) g

let solveLeftBranch rectype g =
  try
    let (lhs,rhs) = match_eqdec_partial (pf_concl g) in
    let (mib,mip) = Global.lookup_inductive rectype in
    let nparams   = mip.mind_nparams in
    let getargs l = list_skipn nparams (snd (decompose_app l)) in
    let rargs   = getargs rhs
    and largs   = getargs lhs in 
    List.fold_right2 
      solveArg largs rargs (tclTHEN h_simplest_left h_reflexivity) g
  with PatternMatchingFailure -> error "Unexpected conclusion!"

(* The tactic Decide Equality *)

let hd_app c = match kind_of_term c with
  | App (h,_) -> h
  | _ -> c

let decideGralEquality g =
  try
    let typ = match_eqdec (pf_concl g) in
    let headtyp = hd_app (pf_compute g typ) in
    let rectype =
      match kind_of_term headtyp with
        | Ind mi -> mi
	| _ -> error "This decision procedure only works for inductive objects"
    in 
    (tclTHEN
      mkBranches 
      (tclORELSE h_solveRightBranch (solveLeftBranch rectype))) g
  with PatternMatchingFailure ->
    error "The goal does not have the expected form"


let decideEquality c1 c2 g = 
  let rectype = (pf_type_of g c1) in     
  let decide  = mkGenDecideEqGoal rectype g in  
  (tclTHENS (cut decide) [default_auto;decideGralEquality]) g


(* The tactic Compare *)

let compare c1 c2 g = 
  let rectype = pf_type_of g c1 in
  let decide  = mkDecideEqGoal rectype c1 c2 g in  
  (tclTHENS (cut decide) 
            [(tclTHEN  intro 
             (tclTHEN (tclLAST_HYP simplest_case)
                       clear_last));
             decideEquality c1 c2]) g


(* User syntax *)

TACTIC EXTEND DecideEquality
  [ "Decide" "Equality" constr(c1) constr(c2) ] -> [ decideEquality c1 c2 ]
| [ "Decide" "Equality" ] -> [ decideGralEquality ]
END

TACTIC EXTEND Compare
| [ "Compare" constr(c1) constr(c2) ] -> [ compare c1 c2 ]
END

