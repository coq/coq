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

(* 
   1- keep track of the instantiations and of ninst in the Sequent.t structure 
   2- ordered instantiations
*)

let ground_tac solver startseq gl=
  let rec toptac seq gl=
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
		   right_tac seq pat l []) gl
  and right_tac seq pat atoms ctx gl=
    let re_add s=re_add_left_list ctx s in
      match pat with
	  Ror->
	    tclORELSE
	    (or_tac toptac (re_add seq))
	    (left_tac seq ctx) gl
	| Rexists(i,dom)->
	    tclORELSE
	    (if seq.depth<=0 || not !qflag then 
	       tclFAIL 0 "max depth" 
	     else 
	       exists_tac i dom atoms toptac (re_add seq))
	    (left_tac seq ctx) gl
	| _-> anomaly "unreachable place"
  and left_tac seq ctx gl=
    if is_empty_left seq then 
      solver gl (* put solver here *)
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
	      tclORELSE
	      (if seq.depth<=0 || not !qflag then 
		 tclFAIL 0 "max depth" 
	       else 
		 left_forall_tac i dom hd.atoms hd.internal hd.id
		    toptac (re_add seq))
	      (left_tac seq1 (hd::ctx)) gl
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
		     (match seq1.gl with 
			  Atomic t->
			    (left_tac seq1 (hd::ctx))
			| Complex (pat,_,atoms)->
			    (right_tac seq1 pat atoms (hd::ctx))) 
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
		 | LLexists (ind,a,p,_) ->
		     if !qflag then
		       ll_ind_tac ind [a;p] hd.id toptac (re_add seq1) 
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
		      
let gen_ground_tac flag taco io l=
  qflag:=flag;
  let depth=
    match io with 
	Some i->i
      | None-> !Auto.default_search_depth in
  let solver= 
    match taco with 
	Some tac->tac
      | None-> default_solver in
  let startseq=create_with_ref_list l depth in
    ground_tac solver startseq

open Genarg
open Pcoq
open Pp

type depth=int option

let pr_depth _ _=function
    None->mt ()
  | Some i -> str " depth " ++ int i

ARGUMENT EXTEND depth TYPED AS depth PRINTED BY pr_depth
[ "depth" integer(i)]-> [ Some i]
| [ ] -> [None]
END 

type with_reflist = global_reference list

let pr_ref_list _ _=function
    [] -> mt ()
  | l -> prlist pr_reference l

TACTIC EXTEND Ground
   [ "Ground" tactic(t) "with" ne_reference_list(l) ] -> 
	 [ gen_ground_tac true (Some (snd t)) None l ]
|   [ "Ground" tactic(t) "depth" integer(i) "with" ne_reference_list(l) ] -> 
	 [ gen_ground_tac true (Some (snd t)) (Some i) l ]
|   [ "Ground" tactic(t) "depth" integer(i) ] -> 
	 [ gen_ground_tac true (Some (snd t)) (Some i) [] ]
|   [ "Ground" tactic(t) ] -> 
	 [ gen_ground_tac true (Some (snd t)) None [] ]
|   [ "Ground" ] ->
	 [ gen_ground_tac true None None [] ]
END

TACTIC EXTEND GTauto   
  [ "GTauto" ] ->
     [ gen_ground_tac false (Some fail_solver) (Some 0) [] ]   
END

TACTIC EXTEND GIntuition
   ["GIntuition" tactic(t)] ->
     [ gen_ground_tac false (Some(snd t)) None [] ]
|  [ "GIntuition" ] ->
     [ gen_ground_tac false None None [] ] 
END

