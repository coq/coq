(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Formula
open Sequent
open Rules
open Instances
open Term
open Tacmach
open Tactics
open Tacticals
      
let ground_tac solver startseq gl=
  let rec toptac skipped seq gl=
    if Tacinterp.get_debug()=Tactic_debug.DebugOn 0
    then Pp.msgnl (Proof_trees.pr_goal (sig_it gl));
    tclORELSE (axiom_tac seq.gl seq)
      begin
	try      
	  let (hd,seq1)=take_formula seq  
	  and re_add s=re_add_formula_list skipped s in
	  let continue=toptac [] 
	  and backtrack=toptac (hd::skipped) seq1  in
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
		      | Ror->
			  tclORELSE
			  (or_tac continue (re_add seq1))
			  backtrack
		      | Rfalse->backtrack 
		      | Rexists(i,dom,triv)->
			  let (lfp,seq2)=collect_quantified seq in
			  let backtrack2=toptac (lfp@skipped) seq2 in
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
			  let backtrack2=toptac (lfp@skipped) seq2 in
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
			  end
		  end
	    with Heap.EmptyHeap->solver
      end gl in
    wrap (List.length (pf_hyps gl)) true (toptac []) (startseq gl) gl
