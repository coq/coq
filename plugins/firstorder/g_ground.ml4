(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma"  i*)

open Formula
open Sequent
open Ground
open Goptions
open Tacticals
open Tacinterp
open Libnames

DECLARE PLUGIN "ground_plugin"

(* declaring search depth as a global option *)

let ground_depth=ref 3

let _=
  let gdopt=
    { optsync=true;
      optdepr=false;
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
      optdepr=false;
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
  Tactic_option.declare_tactic_option ~default:(<:tactic<auto with *>>) "Firstorder default solver"

VERNAC COMMAND EXTEND Firstorder_Set_Solver CLASSIFIED AS SIDEFF
| [ "Set" "Firstorder" "Solver" tactic(t) ] -> [
    set_default_solver 
      (Locality.make_section_locality (Locality.LocalityFixme.consume ()))
      (Tacintern.glob_tactic t) ]
END

VERNAC COMMAND EXTEND Firstorder_Print_Solver CLASSIFIED AS QUERY
| [ "Print" "Firstorder" "Solver" ] -> [
    Pp.msg_info
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
        let seq,gl = extend_with_ref_list ids seq gl in
        extend_with_auto_hints bases seq gl in
      let result=ground_tac (Proofview.V82.of_tactic solver) startseq gl in
	qflag:=backup;result
    with reraise -> qflag:=backup;raise reraise

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

open Pp
open Genarg
open Ppconstr
open Printer
let pr_firstorder_using_raw _ _ _ l = str "using " ++ prlist_with_sep pr_comma pr_reference l
let pr_firstorder_using_glob _ _ _ l = str "using " ++ prlist_with_sep pr_comma (pr_or_var (fun x -> (pr_global (snd x)))) l
let pr_firstorder_using_typed _ _ _ l = str "using " ++ prlist_with_sep pr_comma pr_global l

ARGUMENT EXTEND firstorder_using
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
      [ Proofview.V82.tactic (gen_ground_tac true (Option.map eval_tactic t) l []) ]
|   [ "firstorder" tactic_opt(t) "with" ne_preident_list(l) ] ->
      [ Proofview.V82.tactic (gen_ground_tac true (Option.map eval_tactic t) [] l) ]
|   [ "firstorder" tactic_opt(t) firstorder_using(l)
       "with" ne_preident_list(l') ] ->
      [ Proofview.V82.tactic (gen_ground_tac true (Option.map eval_tactic t) l l') ]
END

TACTIC EXTEND gintuition
  [ "gintuition" tactic_opt(t) ] ->
     [ Proofview.V82.tactic (gen_ground_tac false (Option.map eval_tactic t) [] []) ]
END

open Proofview.Notations

let default_declarative_automation =
  Proofview.tclUNIT () >>= fun () -> (* delay for [congruence_depth] *)
  Tacticals.New.tclORELSE
    (Tacticals.New.tclORELSE (Auto.h_trivial [] None)
    (Cctac.congruence_tac !congruence_depth []))
    (Proofview.V82.tactic (gen_ground_tac true
       (Some (Tacticals.New.tclTHEN
		(snd (default_solver ()))
		(Cctac.congruence_tac !congruence_depth [])))
       [] []))



let () =
  Decl_proof_instr.register_automation_tac default_declarative_automation

