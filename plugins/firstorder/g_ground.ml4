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
open Ground
open Goptions
open Tacmach.New
open Tacticals.New
open Tacinterp
open Stdarg
open Tacarg
open Pcoq.Prim

DECLARE PLUGIN "ground_plugin"

(* declaring search depth as a global option *)

let ground_depth=ref 3

let _=
  let gdopt=
    { optdepr=false;
      optname="Firstorder Depth";
      optkey=["Firstorder";"Depth"];
      optread=(fun ()->Some !ground_depth);
      optwrite=
   (function
	None->ground_depth:=3
      |	Some i->ground_depth:=(max i 0))}
  in
    declare_int_option gdopt


let _=
  let congruence_depth=ref 100 in
  let gdopt=
    { optdepr=true; (* noop *)
      optname="Congruence Depth";
      optkey=["Congruence";"Depth"];
      optread=(fun ()->Some !congruence_depth);
      optwrite=
   (function
        None->congruence_depth:=0
      |	Some i->congruence_depth:=(max i 0))}
  in
    declare_int_option gdopt

let default_intuition_tac =
  let tac _ _ = Auto.h_auto None [] None in
  let name = { Tacexpr.mltac_plugin = "ground_plugin"; mltac_tactic = "auto_with"; } in
  let entry = { Tacexpr.mltac_name = name; mltac_index = 0 } in
  Tacenv.register_ml_tactic name [| tac |];
  Tacexpr.TacML (Loc.tag (entry, []))

let (set_default_solver, default_solver, print_default_solver) = 
  Tactic_option.declare_tactic_option ~default:default_intuition_tac "Firstorder default solver"

VERNAC COMMAND FUNCTIONAL EXTEND Firstorder_Set_Solver CLASSIFIED AS SIDEFF
| [ "Set" "Firstorder" "Solver" tactic(t) ] -> [
    fun ~atts ~st -> let open Vernacinterp in
      set_default_solver
        (Locality.make_section_locality atts.locality)
        (Tacintern.glob_tactic t);
        st
  ]
END

VERNAC COMMAND EXTEND Firstorder_Print_Solver CLASSIFIED AS QUERY
| [ "Print" "Firstorder" "Solver" ] -> [
    Feedback.msg_info
      (Pp.(++) (Pp.str"Firstorder solver tactic is ") (print_default_solver ())) ]
END

let fail_solver=tclFAIL 0 (Pp.str "GTauto failed")

let gen_ground_tac flag taco ids bases =
  let backup= !qflag in
  Proofview.tclOR begin
  Proofview.Goal.enter begin fun gl ->
      qflag:=flag;
      let solver=
	match taco with
	    Some tac-> tac
	  | None-> snd (default_solver ()) in
      let startseq k =
        Proofview.Goal.enter begin fun gl ->
	let seq=empty_seq !ground_depth in
        let seq, sigma = extend_with_ref_list (pf_env gl) (project gl) ids seq in
        let seq, sigma = extend_with_auto_hints (pf_env gl) (project gl) bases seq in
        tclTHEN (Proofview.Unsafe.tclEVARS sigma) (k seq)
        end
      in
      let result=ground_tac solver startseq in
      qflag := backup;
      result
  end
  end
  (fun (e, info) -> qflag := backup; Proofview.tclZERO ~info e)

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
let pr_firstorder_using_raw _ _ _ = Pptactic.pr_auto_using pr_qualid
let pr_firstorder_using_glob _ _ _ = Pptactic.pr_auto_using (pr_or_var (fun x -> pr_global (snd x)))
let pr_firstorder_using_typed _ _ _ = Pptactic.pr_auto_using pr_global

let warn_deprecated_syntax =
  CWarnings.create ~name:"firstorder-deprecated-syntax" ~category:"deprecated"
    (fun () -> Pp.strbrk "Deprecated syntax; use \",\" as separator")


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
    warn_deprecated_syntax ();
    a::b::l
  ]
| [ ] -> [ [] ]
END

TACTIC EXTEND firstorder
    [ "firstorder" tactic_opt(t) firstorder_using(l) ] ->
      [ gen_ground_tac true (Option.map (tactic_of_value ist) t) l [] ]
|   [ "firstorder" tactic_opt(t) "with" ne_preident_list(l) ] ->
      [ gen_ground_tac true (Option.map (tactic_of_value ist) t) [] l ]
|   [ "firstorder" tactic_opt(t) firstorder_using(l)
       "with" ne_preident_list(l') ] ->
      [ gen_ground_tac true (Option.map (tactic_of_value ist) t) l l' ]
END

TACTIC EXTEND gintuition
  [ "gintuition" tactic_opt(t) ] ->
     [ gen_ground_tac false (Option.map (tactic_of_value ist) t) [] [] ]
END
