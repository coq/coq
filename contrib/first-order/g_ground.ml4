(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma"  i*)

(* $Id$ *)

open Formula
open Sequent
open Ground
open Goptions
open Tactics
open Tacticals
open Tacinterp
open Term
open Names
open Util
open Libnames

(* declaring search depth as a global option *)

let ground_depth=ref 5

let _=
  let gdopt=
    { optsync=true;
      optname="Firstorder Depth";
      optkey=SecondaryTable("Firstorder","Depth"); 
      optread=(fun ()->Some !ground_depth); 
      optwrite=
   (function 
	None->ground_depth:=5
      |	Some i->ground_depth:=(max i 0))}
  in
    declare_int_option gdopt
      
let default_solver=(Tacinterp.interp <:tactic<auto with *>>)
    
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
	    Some tac-> tac
	  | None-> default_solver in
      let startseq=
	match ext with
	    Void -> (fun gl -> empty_seq !ground_depth)
	  | Ids l-> create_with_ref_list l !ground_depth
	  | Bases l-> create_with_auto_hints l !ground_depth in
      let result=ground_tac solver startseq gl in 
	qflag:=backup;result
    with e ->qflag:=backup;raise e
      
(* special for compatibility with Intuition 

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

TACTIC EXTEND Firstorder
    [ "Firstorder" tactic_opt(t) "with" ne_reference_list(l) ] -> 
      [ gen_ground_tac true (option_app eval_tactic t) (Ids l) ]
|   [ "Firstorder" tactic_opt(t) "using" ne_preident_list(l) ] -> 
      [ gen_ground_tac true (option_app eval_tactic t) (Bases l) ]
|   [ "Firstorder" tactic_opt(t) ] -> 
      [ gen_ground_tac true (option_app eval_tactic t) Void ]
END

(* Obsolete since V8.0
TACTIC EXTEND GTauto   
  [ "GTauto" ] ->
     [ gen_ground_tac false (Some fail_solver) Void ]   
END
*)

TACTIC EXTEND GIntuition
  [ "GIntuition" tactic_opt(t) ] ->
     [ gen_ground_tac false (option_app eval_tactic t) Void ]
END
