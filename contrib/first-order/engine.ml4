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
open Util

let ground_tac ninst solver gl=
  let metagen=newcnt () in
  let rec toptac ninst seq gl=
    match seq.gl with 
	Atomic t->
	  tclORELSE (axiom_tac t seq) (left_tac ninst seq []) gl
      | Complex (pat,l)->
	  match pat with
	      Rand->and_tac seq (toptac ninst) metagen gl
	    | Rforall->forall_tac seq (toptac ninst) metagen gl
	    | Rarrow->arrow_tac seq (toptac ninst) metagen gl
	    | _->
		if not (is_empty_left seq) && rev_left seq then 
		  left_tac ninst seq [] gl 
		else 
		  right_tac ninst seq pat l [] gl
  and right_tac ninst seq pat atoms ctx gl=
    let re_add s=re_add_left_list ctx s in
      match pat with
	  Ror->
	    tclORELSE
	    (or_tac (re_add seq) (toptac ninst) metagen)
	    (left_tac ninst seq ctx) gl
	| Rexists(i,dom)->
	    tclORELSE
	    (if ninst=0 then tclFAIL 0 "max depth" else 
	       exists_tac i dom atoms (re_add seq) (toptac (ninst-1)) metagen)
	    (left_tac ninst seq ctx) gl
	| _-> anomaly "unreachable place"
  and left_tac ninst seq ctx gl=
    if is_empty_left seq then 
      solver gl (* put solver here *)
    else 
      let (hd,seq1)=take_left seq in 
      let re_add s=re_add_left_list ctx s in 
	match hd.pat with
	    Lfalse->left_false_tac hd.id gl
	  | Land ind->left_and_tac ind hd.id seq1 (toptac ninst) metagen gl
	  | Lor ind->left_or_tac ind hd.id seq1 (toptac ninst) metagen gl
	  | Lforall (i,dom)->
	      tclORELSE
	      (if ninst=0 then tclFAIL 0 "max depth" else 
		 left_forall_tac i dom hd.atoms hd.id (re_add seq)
		   (toptac (ninst-1)) metagen)
	      (left_tac ninst seq1 (hd::ctx)) gl
	  | Lexists ->left_exists_tac hd.id seq1 (toptac ninst) metagen gl
	  | LAatom a->
	      tclORELSE
	      (ll_atom_tac a hd.id (re_add seq1) (toptac ninst) metagen)
	      (match seq1.gl with 
		  Atomic t->
		    (left_tac ninst seq1 (hd::ctx))
		| Complex (pat,atoms)->
		    (right_tac ninst seq1 pat atoms (hd::ctx))) gl
	  | LAfalse->ll_false_tac hd.id seq1 (toptac ninst) metagen gl
	  | LAand (ind,largs) | LAor(ind,largs) ->
	      ll_ind_tac ind largs hd.id seq1 (toptac ninst) metagen gl
	  | LAforall p ->	      
	      tclORELSE
	      (if ninst=0 then tclFAIL 0 "max depth" else 
		 ll_forall_tac p hd.id (re_add seq1) 
		   (toptac (ninst-1)) metagen)
	      (left_tac ninst seq1 (hd::ctx)) gl
	  | LAexists (ind,a,p,_) ->
	      ll_ind_tac ind [a;p] hd.id seq1 (toptac ninst) metagen gl
	  | LAarrow (a,b,c) ->	      
	      tclORELSE
	      (ll_arrow_tac a b c hd.id (re_add seq1) 
		   (toptac ninst) metagen)
	      (left_tac ninst seq1 (hd::ctx)) gl in
  let startseq=create_with_auto_hints gl metagen in
    wrap (List.length (pf_hyps gl)) true empty_seq (toptac ninst) metagen gl

let default_solver=(Tacinterp.interp <:tactic<Auto with *>>)
		     
let gen_ground_tac io taco=
   let depth=
     match io with 
	 Some i->i
       | None-> !Auto.default_search_depth in
   let solver= 
     match taco with 
	 Some t->snd t
       | None-> default_solver in
     ground_tac depth default_solver

TACTIC EXTEND Ground
   [ "Ground" ] -> [ gen_ground_tac None None ]    
|  [ "Ground" integer(n)] -> [ gen_ground_tac (Some n) None]
|  [ "Ground" tactic(t)] -> [ gen_ground_tac None (Some t)]    
|  [ "Ground" integer(n) tactic(t)] -> 
     [ gen_ground_tac (Some n) (Some t) ]
END

 
