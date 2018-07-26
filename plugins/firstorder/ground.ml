(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ltac_plugin
open Formula
open Sequent
open Rules
open Instances
open Tacmach.New
open Tacticals.New
open Globnames

let update_flags ()=
  let f acc coe =
    match coe.Classops.coe_value with
    | ConstRef c -> Names.Cpred.add c acc
    | _ -> acc
  in
    let pred = List.fold_left f Names.Cpred.empty (Classops.coercions ()) in
    red_flags:=
    CClosure.RedFlags.red_add_transparent
      CClosure.betaiotazeta
      (Names.Id.Pred.full,Names.Cpred.complement pred)

let ground_tac solver startseq =
  Proofview.Goal.enter begin fun gl ->
  update_flags ();
  let rec toptac skipped seq =
    Proofview.Goal.enter begin fun gl ->
    let () =
      if Tacinterp.get_debug()=Tactic_debug.DebugOn 0
      then
        let gl = { Evd.it = Proofview.Goal.goal gl; sigma = project gl } in
        Feedback.msg_debug (Printer.pr_goal gl)
    in
    tclORELSE (axiom_tac seq.gl seq)
      begin
	try
	  let (hd,seq1)=take_formula (project gl) seq
	  and re_add s=re_add_formula_list (project gl) skipped s in
	  let continue=toptac []
	  and backtrack =toptac (hd::skipped) seq1 in
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
			  let (lfp,seq2)=collect_quantified (project gl) seq in
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
			  let (lfp,seq2)=collect_quantified (project gl) seq in
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
      end
    end in
    let n = List.length (Proofview.Goal.hyps gl) in
    startseq (fun seq -> wrap n true (toptac []) seq)
  end
