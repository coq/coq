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
open Ground
open Goptions
open Tactics
open Tacticals
open Term
open Names
open Libnames

(* declaring search depth as a global option *)

let ground_depth=ref 5

let _=
  let gdopt=
    { optsync=true;
      optname="Ground Depth";
      optkey=SecondaryTable("Ground","Depth"); 
      optread=(fun ()->Some !ground_depth); 
      optwrite=
   (function 
	None->ground_depth:=5
      |	Some i->ground_depth:=(max i 0))}
  in
    declare_int_option gdopt
      
let default_solver=(Tacinterp.interp <:tactic<Auto with *>>)
    
let fail_solver=tclFAIL 0 "GTauto failed"
		      
type external_env=
    Ids of global_reference list
  | Bases of Auto.hint_db_name list
  | Void

let gen_ground_tac flag taco ext gl=
  let backup= !qflag in
    try
      qflag:=flag;
      let solver= 
	match taco with 
	    Some tac->tac
	  | None-> default_solver in
      let startseq=
	match ext with
	    Void -> (fun gl -> empty_seq !ground_depth)
	  | Ids l-> create_with_ref_list l !ground_depth
	  | Bases l-> create_with_auto_hints l !ground_depth in
      let result=ground_tac solver startseq gl in 
	qflag:=backup;result
    with e ->qflag:=backup;raise e
      
(* special for compatibility with old Intuition 

let constant str = Coqlib.gen_constant "User" ["Init";"Logic"] str

let defined_connectives=lazy
  [[],EvalConstRef (destConst (constant "not"));
   [],EvalConstRef (destConst (constant "iff"))]

let normalize_evaluables=
  onAllClauses
    (function 
	 None->unfold_in_concl (Lazy.force defined_connectives)
       | Some id-> 
	   unfold_in_hyp (Lazy.force defined_connectives) 
	   (Tacexpr.InHypType id)) *)

TACTIC EXTEND Ground
    [ "Ground" tactic(t) "with" ne_reference_list(l) ] -> 
      [ gen_ground_tac true (Some (snd t)) (Ids l) ]
|   [ "Ground" "with" ne_reference_list(l) ] -> 
      [ gen_ground_tac true None (Ids l) ]
|   [ "Ground" tactic(t) "using" ne_preident_list(l) ] -> 
      [ gen_ground_tac true (Some (snd t)) (Bases l) ]
|   [ "Ground" "using" ne_preident_list(l) ] -> 
      [ gen_ground_tac true None (Bases l) ]
|   [ "Ground" tactic(t) ] -> 
      [ gen_ground_tac true (Some (snd t)) Void ]
|   [ "Ground" ] ->
      [ gen_ground_tac true None Void ]
END

TACTIC EXTEND GTauto   
  [ "GTauto" ] ->
     [ gen_ground_tac false (Some fail_solver) Void ]   
END

TACTIC EXTEND GIntuition
   [ "GIntuition" tactic(t) ] ->
     [ gen_ground_tac false (Some (snd t)) Void ]
|  [ "GIntuition" ] ->
     [ gen_ground_tac false (Some default_solver) Void ] 
END

