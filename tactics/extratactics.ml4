(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pp
open Pcoq
open Genarg
open Extraargs

(* Equality *)
open Equality

TACTIC EXTEND Rewrite
  [ "Rewrite" orient(b) constr_with_bindings(c) ] -> [general_rewrite_bindings b c]
END

TACTIC EXTEND RewriteIn
 [ "Rewrite" orient(b) constr_with_bindings(c) "in" ident(h) ] ->
 [general_rewrite_in b h c]
END

let h_rewriteLR x = h_rewrite true (x,Rawterm.NoBindings)

TACTIC EXTEND Replace
  [ "Replace" constr(c1) "with" constr(c2) ] -> [ replace c1 c2 ]
END

TACTIC EXTEND ReplaceIn
  [ "Replace" constr(c1) "with" constr(c2) "in" ident(h) ]
  -> [ failwith "Replace in: TODO" ]
END

TACTIC EXTEND DEq
  [ "Simplify_eq" ident_opt(h) ] -> [ dEq h ]
END

TACTIC EXTEND Discriminate
  [ "Discriminate" ident_opt(h) ] -> [ discr_tac h ]
END

let h_discrHyp id = h_discriminate (Some id)

TACTIC EXTEND Injection
  [ "Injection" ident_opt(h) ] -> [ injClause h ]
END

let h_injHyp id = h_injection (Some id)

TACTIC EXTEND ConditionalRewrite
  [ "Conditional" tactic(tac) "Rewrite" orient(b) constr_with_bindings(c) ]
    -> [ conditional_rewrite b (Tacinterp.interp tac) c ]
END

TACTIC EXTEND ConditionalRewriteIn
  [ "Conditional" tactic(tac) "Rewrite" orient(b) constr_with_bindings(c)
    "in" ident(h) ]
    -> [ conditional_rewrite_in b h (Tacinterp.interp tac) c ]
END

TACTIC EXTEND DependentRewrite
| [ "Dependent" "Rewrite" orient(b) ident(id) ] -> [ substHypInConcl b id ]
| [ "CutRewrite" orient(b) constr(eqn) ] -> [ substConcl b eqn ]
| [ "CutRewrite" orient(b) constr(eqn) "in" ident(id) ]
      -> [ substHyp b eqn id ]
END

(* Contradiction *)
open Contradiction

TACTIC EXTEND Absurd
 [ "Absurd" constr(c) ] -> [ absurd c ]
END

TACTIC EXTEND Contradiction
 [ "Contradiction" ] -> [ contradiction ]
END

(* Inversion *)

open Inv
open Leminv

TACTIC EXTEND SimpleInversion
| [ "Simple" "Inversion" quantified_hypothesis(id) ] -> [ inv None id ]
| [ "Simple" "Inversion" quantified_hypothesis(id) "in" ne_ident_list(l) ]
  -> [ invIn_gen None id l]
| [ "Dependent" "Simple" "Inversion" quantified_hypothesis(id) with_constr(c) ]
  -> [ dinv None c id ]
END

TACTIC EXTEND Inversion
| [ "Inversion" quantified_hypothesis(id) ] -> [ inv (Some false) id ]
| [ "Inversion" quantified_hypothesis(id) "in" ne_ident_list(l) ]
      -> [ invIn_gen (Some false) id l]
| [ "Dependent" "Inversion" quantified_hypothesis(id) with_constr(c) ]
    -> [ dinv (Some false) c id ]
END

TACTIC EXTEND InversionClear
| [ "Inversion_clear" quantified_hypothesis(id) ] -> [ inv (Some true) id ]
| [ "Inversion_clear" quantified_hypothesis(id) "in" ne_ident_list(l) ]
      -> [ invIn_gen (Some true) id l]
| [ "Dependent" "Inversion_clear" quantified_hypothesis(id) with_constr(c) ]
    -> [ dinv (Some true) c id ]
END

TACTIC EXTEND InversionUsing
| [ "Inversion" quantified_hypothesis(id) "using" constr(c) ]
     -> [ lemInv_gen id c ]
| [ "Inversion" quantified_hypothesis(id) "using" constr(c)
    "in" ne_ident_list(l) ]
     -> [ lemInvIn_gen id c l ]
END        

(* AutoRewrite *)

open Autorewrite
TACTIC EXTEND Autorewrite
  [ "AutoRewrite" "[" ne_preident_list(l) "]" ] ->
    [ autorewrite Refiner.tclIDTAC l ]
| [ "AutoRewrite" "[" ne_preident_list(l) "]" "using" tactic(t) ] ->
    [ autorewrite (Tacinterp.interp t) l ]
END

let add_rewrite_hint name ort t lcsr =
  let env = Global.env() and sigma = Evd.empty in
  let f c = Astterm.interp_constr sigma env c, ort, t in
  add_rew_rules name (List.map f lcsr)

VERNAC COMMAND EXTEND HintRewrite
  [ "Hint" "Rewrite" orient(o) "[" ne_constr_list(l) "]" "in" preident(b) ] ->
  [ add_rewrite_hint b o Tacexpr.TacId l ]
| [ "Hint" "Rewrite" orient(o) "[" ne_constr_list(l) "]" "in" preident(b)
    "using" tactic(t) ] ->
  [ add_rewrite_hint b o t l ]
END

(* Refine *)

open Refine

TACTIC EXTEND Refine
  [ "Refine" castedopenconstr(c) ] -> [ refine c ]
END

let refine_tac = h_refine

(* Setoid_replace *)

open Setoid_replace

TACTIC EXTEND SetoidReplace
  [ "Setoid_replace" constr(c1) "with" constr(c2) ]
  -> [ setoid_replace c1 c2 None]
END

TACTIC EXTEND SetoidRewrite
  [ "Setoid_rewrite" orient(b) constr(c) ] -> [ general_s_rewrite b c ]
END

VERNAC COMMAND EXTEND AddSetoid
| [ "Add" "Setoid" constr(a) constr(aeq) constr(t) ] -> [ add_setoid a aeq t ]
| [ "Add" "Morphism" constr(m) ":" ident(s) ] -> [ new_named_morphism s m ]
END

(*
cp tactics/extratactics.ml4 toto.ml; camlp4o -I parsing pa_extend.cmo grammar.cma pr_o.cmo toto.ml 
*)

(* Inversion lemmas (Leminv) *)

VERNAC COMMAND EXTEND DeriveInversionClear
  [ "Derive" "Inversion_clear" ident(na) ident(id) ]
  -> [ inversion_lemma_from_goal 1 na id Term.mk_Prop false inv_clear_tac ]

| [ "Derive" "Inversion_clear" natural(n) ident(na) ident(id) ]
  -> [ inversion_lemma_from_goal n na id Term.mk_Prop false inv_clear_tac ]

| [ "Derive" "Inversion_clear" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s false inv_clear_tac ]

| [ "Derive" "Inversion_clear"  ident(na) "with" constr(c) ]
  -> [ add_inversion_lemma_exn na c (let loc = (0,0) in <:ast< (PROP) >>) false inv_clear_tac ]
END

VERNAC COMMAND EXTEND DeriveInversion
| [ "Derive" "Inversion" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s false half_inv_tac ]

| [ "Derive" "Inversion" ident(na) "with" constr(c) ]
  -> [ add_inversion_lemma_exn na c (let loc = (0,0) in <:ast< (PROP) >>) false half_inv_tac ]

| [ "Derive" "Inversion" ident(na) ident(id) ]
  -> [ inversion_lemma_from_goal 1 na id Term.mk_Prop false half_inv_tac ]

| [ "Derive" "Inversion" natural(n) ident(na) ident(id) ]
  -> [ inversion_lemma_from_goal n na id Term.mk_Prop false half_inv_tac ]
END

VERNAC COMMAND EXTEND DeriveDependentInversion
| [ "Derive" "Dependent" "Inversion" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s true half_dinv_tac ]
    END

VERNAC COMMAND EXTEND DeriveDependentInversionClear
| [ "Derive" "Dependent" "Inversion_clear" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s true dinv_clear_tac ]
END
