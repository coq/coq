(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma"  i*)

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
      optkey=["Firstorder";"Depth"];
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
      optkey=["Congruence";"Depth"];
      optread=(fun ()->Some !congruence_depth);
      optwrite=
   (function
	None->congruence_depth:=0
      |	Some i->congruence_depth:=(max i 0))}
  in
    declare_int_option gdopt

let (set_default_solver, default_solver, print_default_solver) = 
  Tactic_option.declare_tactic_option "Firstorder default solver"

let _ = set_default_solver false (<:tactic<auto with *>>)

VERNAC COMMAND EXTEND Firstorder_Set_Solver
| [ "Set" "Firstorder" "Solver" tactic(t) ] -> [
    set_default_solver 
      (Vernacexpr.use_section_locality ())
      (Tacinterp.glob_tactic t) ]
END

VERNAC COMMAND EXTEND Firstorder_Print_Solver
| [ "Print" "Firstorder" "Solver" ] -> [
    Pp.msgnl
      (Pp.(++) (Pp.str"Firstorder solver tactic is ") (print_default_solver ())) ]
END

let fail_solver=tclFAIL 0 (Pp.str "GTauto failed")

let gen_ground_tac flag taco ids bases gl=
  let backup= !qflag in
    try
      qflag:=flag;
      let solver=
	match taco with
	    Some tac-> tac
	  | None-> snd (default_solver ()) in
      let startseq gl=
	let seq=empty_seq !ground_depth in
	extend_with_auto_hints bases (extend_with_ref_list ids seq gl) gl in
      let result=ground_tac solver startseq gl in
	qflag:=backup;result
    with e ->qflag:=backup;raise e

(* special for compatibility with Intuition

let constant str = Coqlib.gen_constant "User" ["Init";"Logic"] str

let defined_connectives=lazy
  [[],EvalConstRef (destConst (constant "not"));
   [],EvalConstRef (destConst (constant "iff"))]

let normalize_evaluables=
  onAllHypsAndConcl
    (function
	 None->unfold_in_concl (Lazy.force defined_connectives)
       | Some id->
	   unfold_in_hyp (Lazy.force defined_connectives)
	   (Tacexpr.InHypType id)) *)

open Genarg
open Ppconstr
open Printer
let pr_firstorder_using_raw _ _ _ = prlist_with_sep pr_comma pr_reference
let pr_firstorder_using_glob _ _ _ = prlist_with_sep pr_comma (pr_or_var (pr_located pr_global))
let pr_firstorder_using_typed _ _ _ = prlist_with_sep pr_comma pr_global

ARGUMENT EXTEND firstorder_using
  TYPED AS reference_list
  PRINTED BY pr_firstorder_using_typed
  RAW_TYPED AS reference_list
  RAW_PRINTED BY pr_firstorder_using_raw
  GLOB_TYPED AS reference_list
  GLOB_PRINTED BY pr_firstorder_using_glob
| [ "using" reference(a) ] -> [ [a] ]
| [ "using" reference(a) "," ne_reference_list_sep(l,",") ] -> [ a::l ]
| [ "using" reference(a) reference(b) reference_list(l) ] -> [
    Flags.if_verbose
      Pp.msg_warning (Pp.str "Deprecated syntax; use \",\" as separator");
    a::b::l
  ]
| [ ] -> [ [] ]
END

TACTIC EXTEND firstorder
    [ "firstorder" tactic_opt(t) firstorder_using(l) ] ->
      [ gen_ground_tac true (Option.map eval_tactic t) l [] ]
|   [ "firstorder" tactic_opt(t) "with" ne_preident_list(l) ] ->
      [ gen_ground_tac true (Option.map eval_tactic t) [] l ]
|   [ "firstorder" tactic_opt(t) firstorder_using(l)
       "with" ne_preident_list(l') ] ->
      [ gen_ground_tac true (Option.map eval_tactic t) l l' ]
|   [ "firstorder" tactic_opt(t) ] ->
      [ gen_ground_tac true (Option.map eval_tactic t) [] [] ]
END

TACTIC EXTEND gintuition
  [ "gintuition" tactic_opt(t) ] ->
     [ gen_ground_tac false (Option.map eval_tactic t) [] [] ]
END


let default_declarative_automation gls =
  tclORELSE
    (tclORELSE (Auto.h_trivial [] None)
    (Cctac.congruence_tac !congruence_depth []))
    (gen_ground_tac true
       (Some (tclTHEN
		(snd (default_solver ()))
		(Cctac.congruence_tac !congruence_depth [])))
       [] []) gls



let () =
  Decl_proof_instr.register_automation_tac default_declarative_automation

