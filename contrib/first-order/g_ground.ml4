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

let ground_depth=ref 3

let _=
  let gdopt=
    { optsync=true;
      optname="Firstorder Depth";
      optkey=SecondaryTable("Firstorder","Depth"); 
      optread=(fun ()->Some !ground_depth); 
      optwrite=
   (function 
	None->ground_depth:=3
      |	Some i->ground_depth:=(max i 0))}
  in
    declare_int_option gdopt

let congruence_depth=ref 100

let _=
  let gdopt=
    { optsync=true;
      optname="Congruence Depth";
      optkey=SecondaryTable("Congruence","Depth"); 
      optread=(fun ()->Some !congruence_depth); 
      optwrite=
   (function 
	None->congruence_depth:=0
      |	Some i->congruence_depth:=(max i 0))}
  in
    declare_int_option gdopt

let default_solver=(Tacinterp.interp <:tactic<auto with *>>)

let fail_solver=tclFAIL 0 (Pp.str "GTauto failed")
		      
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

TACTIC EXTEND firstorder
    [ "firstorder" tactic_opt(t) "using" ne_reference_list(l) ] -> 
      [ gen_ground_tac true (option_map eval_tactic t) (Ids l) ]
|   [ "firstorder" tactic_opt(t) "with" ne_preident_list(l) ] -> 
      [ gen_ground_tac true (option_map eval_tactic t) (Bases l) ]
|   [ "firstorder" tactic_opt(t) ] -> 
      [ gen_ground_tac true (option_map eval_tactic t) Void ]
END

TACTIC EXTEND gintuition
  [ "gintuition" tactic_opt(t) ] ->
     [ gen_ground_tac false (option_map eval_tactic t) Void ]
END


let default_declarative_automation gls = 
  tclORELSE
    (tclORELSE (Auto.h_trivial [] None) 
    (Cctac.congruence_tac !congruence_depth []))
    (gen_ground_tac true 
       (Some (tclTHEN
		default_solver
		(Cctac.congruence_tac !congruence_depth [])))
       Void) gls



let () = 
  Decl_proof_instr.register_automation_tac default_declarative_automation

