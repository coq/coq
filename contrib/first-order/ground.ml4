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
open Term
open Tacmach
open Tactics
open Tacticals
open Libnames
open Util
open Goptions

let ground_depth=ref 5
		   
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
      

(* 
   1- keep track of the instantiations and of ninst in the Sequent.t structure 
   2- ordered instantiations
*)

let ground_tac solver startseq gl=
  let rec toptac seq gl=
    if Tacinterp.get_debug()=Tactic_debug.DebugOn 
    then Pp.msgnl (Proof_trees.pr_goal (sig_it gl));
    match seq.gl with 
	Atomic t->
	  tclORELSE (axiom_tac t seq) (left_tac seq []) gl
      | Complex (pat,t,l)->
	  tclORELSE (axiom_tac t seq)
	  (match pat with
	       Rand->
		 and_tac toptac seq
	     | Rforall->
		 forall_tac toptac seq
	     | Rarrow->
		 arrow_tac toptac seq
	     | Revaluable egr->
		 evaluable_tac egr toptac seq
	     | _->
		 if not (is_empty_left seq) && rev_left seq then 
		   left_tac seq [] 
		 else 
		   right_tac seq []) gl
  and right_tac seq ctx gl=
    let re_add s=re_add_left_list ctx s in
      match seq.gl with
	  Complex (pat,_,atoms)->
	    (match pat with
		 Ror->
		   tclORELSE
		   (or_tac toptac (re_add seq))
		   (left_tac seq ctx) gl
	       | Rexists(i,dom)->
		   let cont_tac=left_tac seq ctx in
		     if seq.depth<=0 || not !qflag then 
		       cont_tac gl
		     else 
		       (match Unify.give_right_instances i dom atoms seq with
			    Some l -> tclORELSE
			      (exists_tac l toptac (re_add seq)) cont_tac gl
			  | None ->
			      tclORELSE cont_tac
			      (dummy_exists_tac dom  toptac (re_add seq)) gl)
	       | _-> anomaly "unreachable place")
	| Atomic _ -> left_tac seq ctx gl
  and left_tac seq ctx gl=
    if is_empty_left seq then 
      solver gl
    else 
      let (hd,seq1)=take_left seq in 
      let re_add s=re_add_left_list ctx s in 
	match hd.pat with
	    Lfalse->
	      left_false_tac hd.id gl
	  | Land ind->
	      left_and_tac ind hd.id toptac (re_add seq1) gl
	  | Lor ind->
	      left_or_tac ind hd.id toptac (re_add seq1) gl
	  | Lforall (i,dom)->
	      let (lfp,seq2)=collect_forall seq in
		tclORELSE
		  (if seq.depth<=0 || not !qflag then 
		     tclFAIL 0 "max depth" 
		   else 
		     left_forall_tac lfp toptac (re_add seq))
		  (left_tac seq2 (lfp@ctx)) gl
	  | Lexists ->
	      if !qflag then
		left_exists_tac hd.id toptac (re_add seq1) gl
	      else (left_tac seq1 (hd::ctx)) gl
	  | Levaluable egr->
	      left_evaluable_tac egr hd.id toptac (re_add seq1) gl
	  | LA (typ,lap)->
	      tclORELSE
	      (ll_atom_tac typ hd.id toptac (re_add seq1))
	      (match lap with
		   LLatom->
		     right_tac seq1 (hd::ctx) 
		 | LLfalse->
		     ll_false_tac hd.id toptac (re_add seq1) 
		 | LLand (ind,largs) | LLor(ind,largs) ->
		     ll_ind_tac ind largs hd.id toptac (re_add seq1) 
		 | LLforall p ->	      
		     tclORELSE
		     (if seq.depth<=0 || not !qflag then 
			tclFAIL 0 "max depth" 
		      else 
			ll_forall_tac p hd.id toptac (re_add seq1))
		     (left_tac seq1 (hd::ctx))
		 | LLexists (ind,l) ->
		     if !qflag then
		       ll_ind_tac ind l hd.id toptac (re_add seq1) 
		     else
		       left_tac seq1 (hd::ctx)
		 | LLarrow (a,b,c) ->	      
		     tclORELSE
		     (ll_arrow_tac a b c hd.id toptac (re_add seq1))
		     (left_tac seq1 (hd::ctx))
		 | LLevaluable egr->
		     left_evaluable_tac egr hd.id toptac (re_add seq1))
	      gl in
    wrap (List.length (pf_hyps gl)) true toptac (startseq gl) gl
      
let default_solver=(Tacinterp.interp <:tactic<Auto with *>>)
    
let fail_solver=tclFAIL 0 "GroundTauto failed"
		      
let gen_ground_tac flag taco l=
  let backup= !qflag in
    try
      qflag:=flag;
      let solver= 
	match taco with 
	    Some tac->tac
	  | None-> default_solver in
      let startseq=create_with_ref_list l !ground_depth in
      let result=
	ground_tac solver startseq
      in qflag:=backup;result
    with e -> qflag:=backup;raise e
	   
open Genarg
open Pcoq
open Pp

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
     [ gen_ground_tac false (Some(snd t)) [] ]
|  [ "GIntuition" ] ->
     [ gen_ground_tac false None [] ] 
END

