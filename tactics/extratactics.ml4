(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pp
open Pcoq
open Genarg
open Extraargs
open Mod_subst
open Names

(* arnaud:trucs factices *)
type tactic = Tacticals.tactic

module Refiner =
  struct
   let abstract_extended_tactic = Tacticals.abstract_extended_tactic
  end 
let refine _ = Util.anomaly "Extratactics.refine: fantom"
(* arnaud: /trucs factices *)

(* Equality *)
open Equality


TACTIC EXTEND replace 
   ["replace" constr(c1) "with" constr(c2) in_arg_hyp(in_hyp) by_arg_tac(tac) ]
-> [ Util.anomaly "Extratactics.replace: à restaurer" (*arnaud: à restaurer: replace_in_clause_maybe_by c1 c2 (glob_in_arg_hyp_to_clause in_hyp) (Option.map Tacinterp.eval_tactic tac) *)]
END

TACTIC EXTEND replace_term_left
  [ "replace"  "->" constr(c) in_arg_hyp(in_hyp) ]
  -> [ Util.anomaly "Extratactics.replace_term_left: à restaurer" (* arnaud: à restaurer: replace_multi_term (Some true) c (glob_in_arg_hyp_to_clause in_hyp) *)]
END

TACTIC EXTEND replace_term_right
  [ "replace"  "<-" constr(c) in_arg_hyp(in_hyp) ]
  -> [Util.anomaly "Extratactics.replace_term_right: à restaurer" (* arnaud: à restaurer: replace_multi_term (Some false) c (glob_in_arg_hyp_to_clause in_hyp) *)]
END

TACTIC EXTEND replace_term
  [ "replace" constr(c) in_arg_hyp(in_hyp) ]
  -> [ Util.anomaly "Extratactics.replace_term: à restaurer" (* arnaud: à restaurer: replace_multi_term None c (glob_in_arg_hyp_to_clause in_hyp) *)]
END

TACTIC EXTEND simplify_eq
  [ "simplify_eq" quantified_hypothesis_opt(h) ] -> [ Util.anomaly "Extratactics.simplify_eq: à restaurer" (* arnaud: à restaurer: dEq h*) ]
END

TACTIC EXTEND discriminate
  [ "discriminate" quantified_hypothesis_opt(h) ] -> [ Util.anomaly "Extratactics.discriminate: à restaurer" (* arnaud: à restaurer: discr_tac h *) ]
END

let h_discrHyp id = h_discriminate (Some id)

TACTIC EXTEND injection
  [ "injection" quantified_hypothesis_opt(h) ] -> [ Util.anomaly "Extratactics.injection: à restaurer" (* arnaud: à restaurer: injClause [] h*) ]
END 
TACTIC EXTEND injection_as
  [ "injection" quantified_hypothesis_opt(h) 
    "as" simple_intropattern_list(ipat)] -> [ Util.anomaly "Extratactics.injection_as: à restaurer" (* arnaud: à restaurer: injClause ipat h*) ]
END

let h_injHyp id = h_injection (Some id)

TACTIC EXTEND conditional_rewrite
| [ "conditional" tactic(tac) "rewrite" orient(b) constr_with_bindings(c) ]
    -> [ Util.anomaly "Extratactics.conditional_rewrite: à restaurer" (* arnaud: à restaurer: conditional_rewrite b (snd tac) c *) ]
| [ "conditional" tactic(tac) "rewrite" orient(b) constr_with_bindings(c)
    "in" hyp(h) ]
    -> [ Util.anomaly "Extratactics.conditional_rewrite(2): à restaurer" (* arnaud: à restaurer: conditional_rewrite_in b h (snd tac) c *) ]
END

TACTIC EXTEND dependent_rewrite
| [ "dependent" "rewrite" orient(b) constr(c) ] -> [ Util.anomaly "Extratactics.dependent_rewrite: à restaurer" (* arnaud: à restaurer: rewriteInConcl b c *) ]
| [ "dependent" "rewrite" orient(b) constr(c) "in" hyp(id) ]
    -> [ Util.anomaly "Extratactics.dependent_rewrite(2): à restaurer" (* arnaud: à restaurer: rewriteInHyp b c id *) ]
END

TACTIC EXTEND cut_rewrite
| [ "cutrewrite" orient(b) constr(eqn) ] -> [ Util.anomaly "Extratactics.cut_rewrite: à restaurer" (* arnaud: à restaurer: cutRewriteInConcl b eqn *) ]
| [ "cutrewrite" orient(b) constr(eqn) "in" hyp(id) ]
    -> [ Util.anomaly "Extratactics.cut_rewrite(2): à restaurer" (* arnaud: à restaurer: cutRewriteInHyp b eqn id *) ]
END

(* Contradiction *)
open Contradiction

TACTIC EXTEND absurd
 [ "absurd" constr(c) ] -> [ Util.anomaly "Extratactics.absurd: à restaurer" (* arnaud: à restaurer: absurd c *) ]
END

TACTIC EXTEND contradiction
 [ "contradiction" constr_with_bindings_opt(c) ] -> [ Util.anomaly "Extratactics.contradiction: à restaurer" (* arnaud: à restaurer: contradiction c *) ]
END

(* AutoRewrite *)

open Autorewrite
(* arnaud: à dégager ? *)
(* J.F : old version 
TACTIC EXTEND autorewrite
  [ "autorewrite" "with" ne_preident_list(l) ] ->
    [ autorewrite Refiner.tclIDTAC l ]
| [ "autorewrite" "with" ne_preident_list(l) "using" tactic(t) ] ->
    [ autorewrite (snd t) l ]
| [ "autorewrite" "with" ne_preident_list(l) "in" hyp(id) ] ->
    [ autorewrite_in id Refiner.tclIDTAC l ]
| [ "autorewrite" "with" ne_preident_list(l) "in" hyp(id) "using" tactic(t) ] ->
    [ autorewrite_in id (snd t) l ]
END
*)

TACTIC EXTEND autorewrite
| [ "autorewrite" "with" ne_preident_list(l) in_arg_hyp(cl) ] ->
    [ Util.anomaly "Extratactics.autorewrite: à restaurer" (* arnaud: à restaurer: auto_multi_rewrite  l (glob_in_arg_hyp_to_clause  cl) *) ]
| [ "autorewrite" "with" ne_preident_list(l) in_arg_hyp(cl) "using" tactic(t) ] ->
    [ 
      Util.anomaly "Extratactics.autorewrite(2): à restaurer" (* arnaud: à restaurer: let cl =  glob_in_arg_hyp_to_clause cl in 
      auto_multi_rewrite_with (snd t) l cl *)

    ]
END




let add_rewrite_hint name ort t lcsr =
  let env = Global.env() and sigma = Evd.empty in
  let f c = Constrintern.interp_constr sigma env c, ort, t in
  add_rew_rules name (List.map f lcsr)

VERNAC COMMAND EXTEND HintRewrite
  [ "Hint" "Rewrite" orient(o) ne_constr_list(l) ":" preident(b) ] ->
  [ add_rewrite_hint b o (Tacexpr.TacId []) l ]
| [ "Hint" "Rewrite" orient(o) ne_constr_list(l) "using" tactic(t)
    ":" preident(b) ] ->
  [ add_rewrite_hint b o t l ]
END


(* Refine *)

open Refine

TACTIC EXTEND refine
  [ "refine" casted_open_constr(c) ] -> [ refine c ]
END

let refine_tac = h_refine

(* Setoid_replace *)

open Setoid_replace

(* arnaud: à restaurer:
TACTIC EXTEND setoid_replace
   [ "setoid_replace" constr(c1) "with" constr(c2) by_arg_tac(tac)] ->
     [ Util.anomaly "Extratactics.setoid_replace: à restaurer" (* arnaud: à restaurer: setoid_replace  (Option.map Tacinterp.eval_tactic tac) None c1 c2 ~new_goals:[] *) ]
 | [ "setoid_replace" constr(c1) "with" constr(c2) "using" "relation" constr(rel) by_arg_tac(tac)] ->
     [ Util.anomaly "Extratactics.setoid_replace: à restaurer" (* arnaud: à restaurer:setoid_replace  (Option.map Tacinterp.eval_tactic tac) (Some rel) c1 c2 ~new_goals:[] *) ]
 | [ "setoid_replace" constr(c1) "with" constr(c2) "generate" "side" "conditions" constr_list(l) by_arg_tac(tac) ] ->
     [ Util.anomaly "Extratactics.setoid_replace: à restaurer" (* arnaud: à restaurer:setoid_replace  (Option.map Tacinterp.eval_tactic tac) None c1 c2 ~new_goals:l *) ]
 | [ "setoid_replace" constr(c1) "with" constr(c2) "using" "relation" constr(rel) "generate" "side" "conditions" constr_list(l) by_arg_tac(tac) ] ->
     [ Util.anomaly "Extratactics.setoid_replace: à restaurer" (* arnaud: à restaurer:setoid_replace  (Option.map Tacinterp.eval_tactic tac) (Some rel) c1 c2 ~new_goals:l *) ]
 | [ "setoid_replace" constr(c1) "with" constr(c2) "in" hyp(h) by_arg_tac(tac) ] ->
     [ Util.anomaly "Extratactics.setoid_replace: à restaurer" (* arnaud: à restaurer:setoid_replace_in  (Option.map Tacinterp.eval_tactic tac) h None c1 c2 ~new_goals:[] *) ]
 | [ "setoid_replace" constr(c1) "with" constr(c2) "in" hyp(h) "using" "relation" constr(rel) by_arg_tac(tac)] ->
     [ Util.anomaly "Extratactics.setoid_replace: à restaurer" (* arnaud: à restaurer:setoid_replace_in  (Option.map Tacinterp.eval_tactic tac) h (Some rel) c1 c2 ~new_goals:[] *) ]
 | [ "setoid_replace" constr(c1) "with" constr(c2) "in" hyp(h) "generate" "side" "conditions" constr_list(l) by_arg_tac(tac)] ->
     [ Util.anomaly "Extratactics.setoid_replace: à restaurer" (* arnaud: à restaurer:setoid_replace_in  (Option.map Tacinterp.eval_tactic tac) h None c1 c2 ~new_goals:l *) ]
 | [ "setoid_replace" constr(c1) "with" constr(c2) "in" hyp(h) "using" "relation" constr(rel) "generate" "side" "conditions" constr_list(l) by_arg_tac(tac)] ->
     [ Util.anomaly "Extratactics.setoid_replace: à restaurer" (* arnaud: à restaurer:setoid_replace_in  (Option.map Tacinterp.eval_tactic tac) h (Some rel) c1 c2 ~new_goals:l *) ]
END
*)


TACTIC EXTEND setoid_rewrite
   [ "setoid_rewrite" orient(b) constr(c) ]
   -> [ Util.anomaly "Extratactics.setoid_rewrite: à restaurer" (* arnaud: à restaurer: general_s_rewrite b c ~new_goals:[] *) ]
 | [ "setoid_rewrite" orient(b) constr(c) "generate" "side" "conditions" constr_list(l) ]
   -> [ Util.anomaly "Extratactics.setoid_rewrite: à restaurer" (* arnaud: à restaurer: general_s_rewrite b c ~new_goals:l *)  ]
 | [ "setoid_rewrite" orient(b) constr(c) "in" hyp(h) ] ->
      [ Util.anomaly "Extratactics.setoid_rewrite: à restaurer" (* arnaud: à restaurer: general_s_rewrite_in h b c ~new_goals:[] *) ]
 | [ "setoid_rewrite" orient(b) constr(c) "in" hyp(h) "generate" "side" "conditions" constr_list(l) ] ->
      [ Util.anomaly "Extratactics.setoid_rewrite: à restaurer" (* arnaud: à restaurer: general_s_rewrite_in h b c ~new_goals:l *) ]
END

VERNAC COMMAND EXTEND AddSetoid1
  [ "Add" "Setoid" constr(a) constr(aeq) constr(t) "as" ident(n) ] ->
   [ add_setoid n a aeq t ]
| [ "Add" "Morphism" constr(m) ":" ident(n) ] ->
   [ new_named_morphism n m None ]
| [ "Add" "Morphism" constr(m) "with" "signature" morphism_signature(s) "as" ident(n) ] ->
   [ new_named_morphism n m (Some s)]
END

VERNAC COMMAND EXTEND AddRelation1
  [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(t) "symmetry" "proved" "by" constr(t') "as" ident(n) ] ->
   [ add_relation n a aeq (Some t) (Some t') None ]
| [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(t)  "as" ident(n) ] ->
   [ add_relation n a aeq (Some t) None None ]
| [ "Add" "Relation" constr(a) constr(aeq)  "as" ident(n) ] ->
   [ add_relation n a aeq None None None ]
END

VERNAC COMMAND EXTEND AddRelation2
  [ "Add" "Relation" constr(a) constr(aeq) "symmetry" "proved" "by" constr(t') "as" ident(n) ] ->
   [ add_relation n a aeq None (Some t') None ]
| [ "Add" "Relation" constr(a) constr(aeq) "symmetry" "proved" "by" constr(t') "transitivity" "proved" "by" constr(t'')  "as" ident(n) ] ->
   [ add_relation n a aeq None (Some t') (Some t'') ]
END

VERNAC COMMAND EXTEND AddRelation3
  [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(t) "transitivity" "proved" "by" constr(t') "as" ident(n) ] ->
   [ add_relation n a aeq (Some t) None (Some t') ]
| [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(t) "symmetry" "proved" "by" constr(t') "transitivity" "proved" "by" constr(t'') "as" ident(n) ] ->
   [ add_relation n a aeq (Some t) (Some t') (Some t'') ]
| [ "Add" "Relation" constr(a) constr(aeq) "transitivity" "proved" "by" constr(t) "as" ident(n) ] ->
   [ add_relation n a aeq None None (Some t) ]
END

TACTIC EXTEND setoid_symmetry
   [ "setoid_symmetry" ] -> [ Util.anomaly "Extratactics.setoid_symmetry: à restaurer" (* arnaud: à restaurer: setoid_symmetry *) ]
 | [ "setoid_symmetry" "in" hyp(n) ] -> [ Util.anomaly "Extratactics.setoid_symmetry: à restaurer" (* arnaud: à restaurer: setoid_symmetry_in n *) ]
END

(* arnaud: à restaurer
TACTIC EXTEND setoid_reflexivity
   [ "setoid_reflexivity" ] -> [ Util.anomaly "Extratactics.setoid_reflexivity: à restaurer" (* arnaud: à restaurer: setoid_reflexivity *) ]
END

TACTIC EXTEND setoid_transitivity
   [ "setoid_transitivity" constr(t) ] -> [ Util.anomaly "Extratactics.setoid_transitivity: à restaurer" (* arnaud: à restaurer: setoid_transitivity t *) ]
END
*)

(* Inversion lemmas (Leminv) *)

open Inv
open Leminv

VERNAC COMMAND EXTEND DeriveInversionClear
  [ "Derive" "Inversion_clear" ident(na) hyp(id) ]
  -> [ inversion_lemma_from_goal 1 na id Term.mk_Prop false inv_clear_tac ]

| [ "Derive" "Inversion_clear" natural(n) ident(na) hyp(id) ]
  -> [ inversion_lemma_from_goal n na id Term.mk_Prop false inv_clear_tac ]

| [ "Derive" "Inversion_clear" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s false inv_clear_tac ]

| [ "Derive" "Inversion_clear" ident(na) "with" constr(c) ]
  -> [ add_inversion_lemma_exn na c (Rawterm.RProp Term.Null) false inv_clear_tac ]
END

open Term
open Rawterm

VERNAC COMMAND EXTEND DeriveInversion
| [ "Derive" "Inversion" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s false inv_tac ]

| [ "Derive" "Inversion" ident(na) "with" constr(c) ]
  -> [ add_inversion_lemma_exn na c (RProp Null) false inv_tac ]

| [ "Derive" "Inversion" ident(na) hyp(id) ]
  -> [ inversion_lemma_from_goal 1 na id Term.mk_Prop false inv_tac ]

| [ "Derive" "Inversion" natural(n) ident(na) hyp(id) ]
  -> [ inversion_lemma_from_goal n na id Term.mk_Prop false inv_tac ]
END

VERNAC COMMAND EXTEND DeriveDependentInversion
| [ "Derive" "Dependent" "Inversion" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s true dinv_tac ]
    END

VERNAC COMMAND EXTEND DeriveDependentInversionClear
| [ "Derive" "Dependent" "Inversion_clear" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s true dinv_clear_tac ]
END

(* Subst *)

TACTIC EXTEND subst
| [ "subst" ne_var_list(l) ] -> [ Util.anomaly "Extratactics.subst: à restaurer" (* arnaud: à restaurer: subst l *) ]
| [ "subst" ] -> [ Util.anomaly "Extratactics.subst: à restaurer" (* arnaud: à restaurer: subst_all *) ]
END

open Evar_tactics

(* evar creation *)

TACTIC EXTEND evar
  [ "evar" "(" ident(id) ":" lconstr(typ) ")" ] -> [ Util.anomaly "Extratactics.evar: à restaurer" (* arnaud: à restaurer: let_evar (Name id) typ *) ]
| [ "evar" constr(typ) ] -> [ Util.anomaly "Extratactics.evar(2): à restaurer" (* arnaud: à restaurer: let_evar Anonymous typ *)]
END

open Tacexpr

TACTIC EXTEND instantiate
  [ "instantiate" "(" integer(i) ":=" raw(c) ")" hloc(hl) ] ->
    [Util.anomaly "Extratactics.instantiate: à restaurer" (* arnaud: à restaurer: instantiate i c hl *) ]
END


(** Nijmegen "step" tactic for setoid rewriting *)

open Tacticals
open Tactics
open Tactics
open Libnames
open Rawterm
open Summary
open Libobject
open Lib

(* Registered lemmas are expected to be of the form
     x R y -> y == z -> x R z    (in the right table)
     x R y -> x == z -> z R y    (in the left table)
*)

let transitivity_right_table = ref []
let transitivity_left_table = ref []

(* [step] tries to apply a rewriting lemma; then apply [tac] intended to
   complete to proof of the last hypothesis (assumed to state an equality) *)

let step left x tac =
  let l =
    List.map (fun lem ->
      tclTHENLAST
      (apply_with_bindings (lem, ImplicitBindings [x]))
        tac)
      !(if left then transitivity_left_table else transitivity_right_table)
  in
  tclFIRST l

(* Main function to push lemmas in persistent environment *)

let cache_transitivity_lemma (_,(left,lem)) =
  if left then  
    transitivity_left_table  := lem :: !transitivity_left_table
  else
    transitivity_right_table := lem :: !transitivity_right_table
  
let subst_transitivity_lemma (_,subst,(b,ref)) = (b,subst_mps subst ref)

let (inTransitivity,_) =
  declare_object {(default_object "TRANSITIVITY-STEPS") with
    cache_function = cache_transitivity_lemma;
    open_function = (fun i o -> if i=1 then cache_transitivity_lemma o);
    subst_function = subst_transitivity_lemma;
    classify_function = (fun (_,o) -> Substitute o);       
    export_function = (fun x -> Some x) }

(* Synchronisation with reset *)

let freeze () = !transitivity_left_table, !transitivity_right_table

let unfreeze (l,r) = 
  transitivity_left_table := l;
  transitivity_right_table := r

let init () = 
  transitivity_left_table := [];
  transitivity_right_table := []

let _ = 
  declare_summary "transitivity-steps"
    { freeze_function = freeze;
      unfreeze_function = unfreeze;
      init_function = init;
      survive_module = false; 
      survive_section = false }

(* Main entry points *)

let add_transitivity_lemma left lem =
 let lem' = Constrintern.interp_constr Evd.empty (Global.env ()) lem in
  add_anonymous_leaf (inTransitivity (left,lem'))

(* Vernacular syntax *)

TACTIC EXTEND stepl
| ["stepl" constr(c) "by" tactic(tac) ] -> [ Util.anomaly "Extratactics.stepl: à restaurer" (* arnaud: à restaurer: step true c (snd tac) *) ]
| ["stepl" constr(c) ] -> [  Util.anomaly "Extratactics.stepl: à restaurer" (* arnaud: à restaurer: step true c tclIDTAC *) ]
END

TACTIC EXTEND stepr
| ["stepr" constr(c) "by" tactic(tac) ] -> [  Util.anomaly "Extratactics.stepr: à restaurer" (* arnaud: à restaurer: step false c (snd tac) *) ]
| ["stepr" constr(c) ] -> [  Util.anomaly "Extratactics.stepr(2): à restaurer" (* arnaud: à restaurer: step false c tclIDTAC *) ]
END

VERNAC COMMAND EXTEND AddStepl
| [ "Declare" "Left" "Step" constr(t) ] ->
    [ add_transitivity_lemma true t ]
END

VERNAC COMMAND EXTEND AddStepr
| [ "Declare" "Right" "Step" constr(t) ] ->
    [ add_transitivity_lemma false t ]
END

VERNAC COMMAND EXTEND ImplicitTactic
| [ "Declare" "Implicit" "Tactic" tactic(tac) ] ->
    [ Tacinterp.declare_implicit_tactic (Tacinterp.interp tac) ]
END




(*spiwack : Vernac commands for retroknowledge *)

VERNAC COMMAND EXTEND RetroknowledgeRegister
 | [ "Register" constr(c) "as" retroknowledge_field(f) "by" constr(b)] -> 
           [ let tc = Constrintern.interp_constr Evd.empty (Global.env ()) c in
             let tb = Constrintern.interp_constr Evd.empty (Global.env ()) b in
             Global.register f tc tb ]
END


(* /spiwack *)


TACTIC EXTEND apply_in
| ["apply" constr_with_bindings(c) "in" hyp(id) ] -> [ Util.anomaly "Extratactics.apply_in: à restaurer" (* arnaud: à restaurer: apply_in false id [c] *) ]
| ["apply" constr_with_bindings(c) "," constr_with_bindings_list_sep(cl,",") 
   "in" hyp(id) ] -> [ Util.anomaly "Extratactics.apply_in: à restaurer" (* arnaud: à restaurer: apply_in false id (c::cl) *) ]
END


TACTIC EXTEND eapply_in
| ["eapply" constr_with_bindings(c) "in" hyp(id) ] -> [  Util.anomaly "Extratactics.eapply_in: à restaurer" (* arnaud: à restaurer: apply_in true id [c] *) ]
| ["epply" constr_with_bindings(c) "," constr_with_bindings_list_sep(cl,",") 
   "in" hyp(id) ] -> [ Util.anomaly "Extratactics.eapply_in: à restaurer" (* arnaud: à restaurer: apply_in true id (c::cl) *) ]
END

(* sozeau: abs/gen for induction on instantiated dependent inductives, using "Ford" induction as 
  defined by Conor McBride *)
TACTIC EXTEND generalize_eqs
| ["generalize_eqs" hyp(id) ] -> [ Util.anomaly "Extratactics.generalize_eqs: à restaurer" (* arnaud: à restaurer: abstract_generalize id *) ]
END

