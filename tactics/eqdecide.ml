(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Util
open Names
open Term
open Tactics
open Tacticals
open Hiddentac
open Equality
open Auto
open Pattern
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

let clear_last = (tclLAST_HYP (fun c -> (clear_one (destVar c))))

let mkBranches = 
        (tclTHEN  intro 
        (tclTHEN (tclLAST_HYP h_simplest_elim)
        (tclTHEN  clear_last
        (tclTHEN  intros 
        (tclTHEN (tclLAST_HYP h_simplest_case)
        (tclTHEN  clear_last
                  intros))))))

let solveRightBranch  = (tclTHEN h_simplest_right h_discrConcl)

let h_solveRightBranch =
  hide_atomic_tactic "solveRightBranch" solveRightBranch


(* Constructs the type {c1=c2}+{~c1=c2} *)

let mkDecideEqGoal rectype c1 c2 g = 
  let equality    = mkAppA [|build_coq_eq_data.eq (); rectype; c1; c2|] in
  let disequality = mkAppA [|build_coq_not (); equality|] in
  mkAppA [|build_coq_sumbool (); equality; disequality |]


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
  (tclTHEN (tclLAST_HYP h_rewriteLR)
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
  (tclTHEN  (h_injHyp absurd)
            full_trivial))))))

let solveArg a1 a2 tac  g = 
  let rectype = pf_type_of g a1 in
  let decide  = mkDecideEqGoal rectype a1 a2 g in  
  (tclTHENS
     (h_elimType decide) 
     [(eqCase tac);diseqCase;default_auto]) g

let solveLeftBranch rectype g =
  match
    try matches (Coqlib.build_coq_eqdec_partial_pattern ()) (pf_concl g)
    with Pattern.PatternMatchingFailure -> error "Unexpected conclusion!"
  with 
    | _ :: lhs :: rhs :: _ -> 
	let nparams   = Global.mind_nparams rectype in
	let getargs l = snd (list_chop nparams (snd (decomp_app l))) in
	let rargs   = getargs (snd rhs)
	and largs   = getargs (snd lhs) in 
	List.fold_right2 
	  solveArg largs rargs (tclTHEN h_simplest_left h_reflexivity) g
    | _ -> anomaly "Unexpected pattern for solveLeftBranch"


(* The tactic Decide Equality *)

let hd_app c = match kind_of_term c with
  | IsApp (h,_) -> h
  | _ -> c

let decideGralEquality g =
  match
    try matches (build_coq_eqdec_pattern ()) (pf_concl g)
    with Pattern.PatternMatchingFailure ->
      error "The goal does not have the expected form"
  with 
    | (_,typ) :: _ ->
	let headtyp = hd_app (pf_compute g typ) in
	let rectype =
	  match kind_of_term headtyp with
            | IsMutInd mi -> mi
	    | _ -> error 
		"This decision procedure only works for inductive objects" 
	in 
	(tclTHEN
	   mkBranches 
           (tclORELSE h_solveRightBranch (solveLeftBranch rectype))) g
    | _ -> anomaly "Unexpected pattern for decideGralEquality"


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


(* The dynamic tactics to be registered in the tactics table *)

let dyn_decideEquality args g = match args with 
  | [ Constr c1; Constr c2 ] -> 
      decideEquality c1 c2 g 
  | [ Command com1; Command com2 ] -> 
      let c1 = pf_interp_constr g com1
      and c2 = pf_interp_constr g com2 in  
      decideEquality c1 c2 g 
  | [] -> decideGralEquality g
  | _  -> error "Invalid arguments for dynamic tactic"

let dyn_compare args g = match args with 
  | [ Constr c1; Constr c2 ] -> 
      compare c1 c2 g
  | [ Command com1; Command com2 ] -> 
      let c1 = pf_interp_constr g com1
      and c2 = pf_interp_constr g com2 in  
      compare c1 c2 g
  | _  ->  error "Invalid arguments for dynamic tactic"
 

(* Tactic registration *)

let _ = add_tactic "DecideEquality" dyn_decideEquality
let _ = add_tactic "Compare"        dyn_compare


