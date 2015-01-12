(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Formula
open Sequent
open Rules
open Instances
open Term
open Tacmach
open Tacticals

let update_flags ()=
  let predref=ref Names.Cpred.empty in
  let f coe=
    try
      let kn= fst (destConst (Classops.get_coercion_value coe)) in
	predref:=Names.Cpred.add kn !predref
    with DestKO -> ()
  in
    List.iter f (Classops.coercions ());
    red_flags:=
    Closure.RedFlags.red_add_transparent
      Closure.betaiotazeta
      (Names.Id.Pred.full,Names.Cpred.complement !predref)

let ground_tac solver startseq gl=
  update_flags ();
  let rec toptac skipped seq gl=
    if Tacinterp.get_debug()=Tactic_debug.DebugOn 0
    then Pp.msg_debug (Printer.pr_goal gl);
    tclORELSE (axiom_tac seq.gl seq)
      begin
	try
	  let (hd,seq1)=take_formula seq
	  and re_add s=re_add_formula_list skipped s in
	  let continue=toptac []
	  and backtrack gl=toptac (hd::skipped) seq1 gl in
	    match hd.pat with
		Right rpat->
		  begin
		    match rpat with
			Rand->
			  and_tac backtrack continue (re_add seq1)
		      | Rforall->
			  let backtrack1=
			    if !qflag then
			      tclFAIL 0 (Pp.str "reversible in 1st order mode")
			    else
			      backtrack in
			    forall_tac backtrack1 continue (re_add seq1)
		      | Rarrow->
			  arrow_tac backtrack continue (re_add seq1)
		      | Ror->
			  or_tac  backtrack continue (re_add seq1)
		      | Rfalse->backtrack
		      | Rexists(i,dom,triv)->
			  let (lfp,seq2)=collect_quantified seq in
			  let backtrack2=toptac (lfp@skipped) seq2 in
			    if  !qflag && seq.depth>0 then
			      quantified_tac lfp backtrack2
				continue (re_add seq)
			    else
			      backtrack2 (* need special backtracking *)
		  end
	      | Left lpat->
		  begin
		    match lpat with
			Lfalse->
			  left_false_tac hd.id
		      | Land ind->
			  left_and_tac ind backtrack
			  hd.id continue (re_add seq1)
		      | Lor ind->
			  left_or_tac ind backtrack
			  hd.id continue (re_add seq1)
		      | Lforall (_,_,_)->
			  let (lfp,seq2)=collect_quantified seq in
			  let backtrack2=toptac (lfp@skipped) seq2 in
			    if  !qflag && seq.depth>0 then
			      quantified_tac lfp backtrack2
				continue (re_add seq)
			    else
			      backtrack2 (* need special backtracking *)
  		      | Lexists ind ->
			  if !qflag then
			    left_exists_tac ind backtrack hd.id
			      continue (re_add seq1)
			  else backtrack
		      | LA (typ,lap)->
			  let la_tac=
			    begin
			      match lap with
				  LLatom -> backtrack
				| LLand (ind,largs) | LLor(ind,largs)
				| LLfalse (ind,largs)->
				    (ll_ind_tac ind largs backtrack
				       hd.id continue (re_add seq1))
				| LLforall p ->
				    if seq.depth>0 && !qflag then
				      (ll_forall_tac p backtrack
					 hd.id continue (re_add seq1))
				    else backtrack
				| LLexists (ind,l) ->
				    if !qflag then
				      ll_ind_tac ind l backtrack
					hd.id continue (re_add seq1)
				    else
				      backtrack
				| LLarrow (a,b,c) ->
				    (ll_arrow_tac a b c backtrack
				       hd.id continue (re_add seq1))
			    end in
			    ll_atom_tac typ la_tac hd.id continue (re_add seq1)
		  end
	    with Heap.EmptyHeap->solver
      end gl in
    let seq, gl' = startseq gl in
    wrap (List.length (pf_hyps gl)) true (toptac []) seq gl'

