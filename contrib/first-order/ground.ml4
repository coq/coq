(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma"  i*)

(* $Id$ *)

open Formula
open Sequent
open Rules
open Instances
open Term
open Tacmach
open Tactics
open Tacticals
open Libnames
open Util
open Goptions

(* declaring search depth as a global option *)

let ground_depth=ref 5

let set_qflag b= qflag:=b
		   
let _=
  let gdopt=
    { optsync=false;
      optname="ground_depth";
      optkey=SecondaryTable("Ground","Depth"); 
      optread=(fun ()->Some !ground_depth); 
      optwrite=
   (function 
	None->ground_depth:=5
      |	Some i->ground_depth:=(max i 0))}
  in
    declare_int_option gdopt
      
let ground_tac solver startseq gl=
  let rec toptac ctx seq gl=
    if Tacinterp.get_debug()=Tactic_debug.DebugOn 0
    then Pp.msgnl (Proof_trees.pr_goal (sig_it gl));
    tclORELSE (axiom_tac seq.gl seq)
      begin
	try      
	  let (hd,seq1)=take_formula seq  
	  and re_add s=re_add_formula_list ctx s in
	  let continue=toptac [] 
	  and backtrack=toptac (hd::ctx) seq1  in
	    match hd.pat with
		Right rpat->
		  begin
		    match rpat with
			Rand->
			  and_tac continue (re_add seq1)
		      | Rforall->
			  forall_tac continue (re_add seq1)
		      | Rarrow->
			  arrow_tac continue (re_add seq1)
		      | Revaluable egr->
			  evaluable_tac egr continue (re_add seq1)
		      | Ror->
			  tclORELSE
			  (or_tac continue (re_add seq1))
			  backtrack
		      | Rfalse->backtrack 
		      | Rexists(i,dom,triv)->
			  let (lfp,seq2)=collect_quantified seq in
			  let backtrack2=toptac (lfp@ctx) seq2 in
			    tclORELSE
			      (if seq.depth<=0 || not !qflag then 
				 tclFAIL 0 "max depth" 
			       else 
				 quantified_tac lfp continue (re_add seq1))
			      backtrack2 (* need special backtracking *)
		  end
	      | Left lpat->
		  begin
		    match lpat with
			Lfalse->
			  left_false_tac hd.id
		      | Land ind->
			  left_and_tac ind hd.id continue (re_add seq1)
		      | Lor ind->
			  left_or_tac ind hd.id continue (re_add seq1)
		      | Lforall (_,_,_)->
			  let (lfp,seq2)=collect_quantified seq in
			  let backtrack2=toptac (lfp@ctx) seq2 in
			    tclORELSE
			      (if seq.depth<=0 || not !qflag then 
				 tclFAIL 0 "max depth" 
			       else 
				 quantified_tac lfp continue (re_add seq))
			      backtrack2 (* need special backtracking *)
		      | Lexists ind ->
			  if !qflag then
			    left_exists_tac ind hd.id continue (re_add seq1)
			  else backtrack
		      | Levaluable egr->
			  left_evaluable_tac egr hd.id continue (re_add seq1)
		      | LA (typ,lap)->
			  tclORELSE
			  (ll_atom_tac typ hd.id continue (re_add seq1))
			  begin
			    match lap with
				LLatom -> backtrack 
			      | LLand (ind,largs) | LLor(ind,largs) 
			      | LLfalse (ind,largs)->
				  (ll_ind_tac ind largs hd.id continue 
				     (re_add seq1)) 
			      | LLforall p ->	      
				  if seq.depth<=0 || not !qflag then 
				    backtrack 
				  else
				    tclORELSE
				      (ll_forall_tac p hd.id continue 
					 (re_add seq1))
				      backtrack
			      | LLexists (ind,l) ->
				  if !qflag then
				    ll_ind_tac ind l hd.id continue 
				      (re_add seq1)
				  else
				    backtrack
			      | LLarrow (a,b,c) ->	      
				  tclORELSE
				  (ll_arrow_tac a b c hd.id continue 
				     (re_add seq1))
				  backtrack
			      | LLevaluable egr->
				  left_evaluable_tac egr hd.id continue 
				  (re_add seq1)
			  end
		  end
	    with Heap.EmptyHeap->solver
      end gl in
    wrap (List.length (pf_hyps gl)) true (toptac []) (startseq gl) gl
      
let default_solver=(Tacinterp.interp <:tactic<Auto with *>>)
    
let fail_solver=tclFAIL 0 "GroundTauto failed"
		      
let gen_ground_tac flag taco l gl=
  let backup= !qflag in
    try
      set_qflag flag;
      let solver= 
	match taco with 
	    Some tac->tac
	  | None-> default_solver in
      let startseq=create_with_ref_list l !ground_depth in
      let result=ground_tac solver startseq gl in 
	set_qflag backup;result
    with e -> set_qflag backup;raise e
	   
TACTIC EXTEND Ground
      |   [ "Ground" tactic(t) "with" ne_reference_list(l) ] -> 
	    [ gen_ground_tac true (Some (snd t)) l ]
      |   [ "Ground" tactic(t) ] -> 
	    [ gen_ground_tac true (Some (snd t)) [] ]
      |   [ "Ground" "with" ne_reference_list(l) ] -> 
	    [ gen_ground_tac true None l ]
      |   [ "Ground" ] ->
	    [ gen_ground_tac true None [] ]
END

TACTIC EXTEND GTauto   
  [ "GTauto" ] ->
     [ gen_ground_tac false (Some fail_solver) [] ]   
END

TACTIC EXTEND GIntuition
   ["GIntuition" tactic(t)] ->
     [ gen_ground_tac false 
	 (Some(tclTHEN normalize_evaluables (snd t))) [] ]
|  [ "GIntuition" ] ->
     [ gen_ground_tac false 
	 (Some (tclTHEN normalize_evaluables default_solver)) [] ] 
END

