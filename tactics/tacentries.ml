
(* $Id$ *)

open Proof_trees
open Tacmach
open Tactics
open Tacticals

let v_absurd        = hide_tactic "Absurd"        dyn_absurd
let v_contradiction = hide_tactic "Contradiction" dyn_contradiction
let v_reflexivity   = hide_tactic "Reflexivity"   dyn_reflexivity
let v_symmetry      = hide_tactic "Symmetry"      dyn_symmetry
let v_transitivity  = hide_tactic "Transitivity"  dyn_transitivity
let v_intro         = hide_tactic "Intro"         dyn_intro
let v_intro_move    = hide_tactic "IntroMove"     dyn_intro_move
let v_introsUntil   = hide_tactic "IntrosUntil"   dyn_intros_until
(*i let v_tclIDTAC      = hide_tactic "Idtac"         dyn_tclIDTAC
let v_tclFAIL       = hide_tactic "Fail"          dyn_tclFAIL i*)
let v_assumption    = hide_tactic "Assumption"    dyn_assumption
let v_exact         = hide_tactic "Exact"         dyn_exact_check
let v_reduce        = hide_tactic "Reduce"        dyn_reduce
let v_change        = hide_tactic "Change"        dyn_change
let v_constructor   = hide_tactic "Constructor"   dyn_constructor
let v_left          = hide_tactic "Left"          dyn_left
let v_right         = hide_tactic "Right"         dyn_right
let v_split         = hide_tactic "Split"         dyn_split
let v_clear         = hide_tactic "Clear"         dyn_clear
let v_move          = hide_tactic "Move"          dyn_move
let v_move_dep      = hide_tactic "MoveDep"       dyn_move_dep
let v_apply         = hide_tactic "Apply"         dyn_apply
let v_cutAndResolve = hide_tactic "CutAndApply"   dyn_cut_and_apply
let v_cut           = hide_tactic "Cut"           dyn_cut
let v_lettac        = hide_tactic "LetTac"        dyn_lettac
let v_generalize    = hide_tactic "Generalize"    dyn_generalize
let v_generalize_dep = hide_tactic "GeneralizeDep" dyn_generalize_dep
let v_specialize    = hide_tactic "Specialize"    dyn_new_hyp
let v_elim          = hide_tactic "Elim"          dyn_elim
let v_elimType      = hide_tactic "ElimType"      dyn_elim_type
let v_induction     = hide_tactic "Induction"     dyn_old_induct
let v_new_induction = hide_tactic "NewInduction"  dyn_new_induct
let v_case          = hide_tactic "Case"          dyn_case
let v_caseType      = hide_tactic "CaseType"      dyn_case_type
let v_destruct      = hide_tactic "Destruct"      dyn_destruct
let v_fix           = hide_tactic "Fix"           dyn_mutual_fix
let v_cofix         = hide_tactic "Cofix"         dyn_mutual_cofix

