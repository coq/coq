(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$: *)

Declare ML Module "equality".

Grammar tactic simple_tactic: ast :=
  replace [ "Replace" constrarg($c1) "with" constrarg($c2) ] -> [(Replace $c1 $c2)]

| deqhyp   [ "Simplify_eq" identarg($id) ] -> [(DEqHyp $id)]
| deqconcl [ "Simplify_eq" ] -> [(DEqConcl)]

| discr_id [ "Discriminate" identarg($id) ] -> [(DiscrHyp $id)]
| discr    [ "Discriminate" ] -> [(Discr)]

| inj    [ "Injection" ] -> [(Inj)]
| inj_id [ "Injection" identarg($id) ] -> [(InjHyp $id)]

| rewriteLR [ "Rewrite" "->" constrarg_binding_list($cl) ] -> [(RewriteLR ($LIST $cl))]
| rewriteRL [ "Rewrite" "<-" constrarg_binding_list($cl) ] -> [(RewriteRL ($LIST $cl))]
| rewrite [ "Rewrite" constrarg_binding_list($cl) ] -> [(RewriteLR ($LIST $cl))]

| condrewriteLR [ "Conditional" tactic_expr($tac) "Rewrite" "->" constrarg_binding_list($cl) ] -> [(CondRewriteLR (TACTIC $tac) ($LIST $cl))]
| condrewriteRL [ "Conditional" tactic_expr($tac) "Rewrite" "<-" constrarg_binding_list($cl) ] -> [(CondRewriteRL (TACTIC $tac) ($LIST $cl))]
| condrewrite [ "Conditional" tactic_expr($tac) "Rewrite" constrarg_binding_list($cl) ] -> [(CondRewriteLR (TACTIC $tac) ($LIST $cl))]

| rewrite_in [ "Rewrite" constrarg_binding_list($cl) "in" identarg($h) ]
       -> [(RewriteLRin $h ($LIST $cl))]
| rewriteRL_in [ "Rewrite" "->" constrarg_binding_list($cl) "in" identarg($h) ]
       -> [(RewriteLRin $h ($LIST $cl))]
| rewriteLR_in [ "Rewrite" "<-" constrarg_binding_list($cl) "in" identarg($h) ]
       -> [(RewriteRLin $h ($LIST $cl))]

| condrewriteLRin 
  [ "Conditional" tactic_expr($tac) "Rewrite" "->" constrarg_binding_list($cl) 
	"in" identarg($h) ] ->
	   [(CondRewriteLRin (TACTIC $tac) $h ($LIST $cl))]
| condrewriteRLin 
  [ "Conditional" tactic_expr($tac) "Rewrite" "<-" constrarg_binding_list($cl) 
	"in" identarg($h)] ->
  	   [(CondRewriteRLin (TACTIC $tac) $h ($LIST $cl))]
| condrewritein 
  [ "Conditional" tactic_expr($tac) "Rewrite" constrarg_binding_list($cl) "in" identarg($h) ] 
        -> [(CondRewriteLRin (TACTIC $tac) $h ($LIST $cl))]

| DRewriteLR [ "Dependent" "Rewrite" "->" identarg($id) ]
       -> [(SubstHypInConcl_LR $id)]
| DRewriteRL [ "Dependent" "Rewrite" "<-" identarg($id) ]
       -> [(SubstHypInConcl_RL $id)]

| cutrewriteLR [ "CutRewrite" "->" constrarg($eqn) ] -> [(SubstConcl_LR $eqn)]
| cutrewriteLRin [ "CutRewrite" "->" constrarg($eqn) "in" identarg($id) ]
      -> [(SubstHyp_LR $eqn $id)]
| cutrewriteRL [ "CutRewrite" "<-" constrarg($eqn) ] -> [(SubstConcl_RL $eqn)]
| cutrewriteRLin [ "CutRewrite" "<-" constrarg($eqn) "in" identarg($id) ]
      -> [(SubstHyp_RL $eqn $id)].

Syntax tactic level 0:
  replace [<<(Replace $c1 $c2)>>] -> ["Replace " $c1 [1 1] "with " $c2]

| deqhyp [<<(DEqHyp $id)>>] -> ["Simplify_eq " $id]
| deqconcl [<<(DEqConcl)>>] -> ["Simplify_eq"]

| discr_id [<<(DiscrHyp $id)>>] -> ["Discriminate " $id]
| discr [<<(Discr)>>] -> ["Discriminate"]

| inj [<<(Inj)>>] -> ["Injection"]
| inj_id [<<(InjHyp $id)>>] -> ["Injection " $id]

| rewritelr [<<(RewriteLR $C ($LIST $bl))>>] -> ["Rewrite " $C (WITHBINDING ($LIST $bl))]
| rewriterl [<<(RewriteRL $C ($LIST $bl))>>] -> ["Rewrite <- " $C (WITHBINDING ($LIST $bl))]

| condrewritelr [<<(CondRewriteLR (TACTIC $tac) $C ($LIST $bl))>>] -> ["Conditional " $tac [1 1] "Rewrite " $C (WITHBINDING ($LIST $bl))]
| condrewriterl [<<(CondRewriteRL (TACTIC $tac) $C ($LIST $bl))>>] -> ["Conditional "  $tac [1 1] "Rewrite <- " $C (WITHBINDING ($LIST $bl))]

| rewriteLR_in [<<(RewriteLRin $h $c ($LIST $bl))>>] -> ["Rewrite " $c (WITHBINDING ($LIST $bl)) [1 1] "in " $h]
| rewriteRL_in [<<(RewriteRLin $h $c ($LIST $bl))>>] -> ["Rewrite <- " $c (WITHBINDING ($LIST $bl)) [1 1]"in " $h]

| condrewritelrin [<<(CondRewriteLRin (TACTIC $tac) $h $C ($LIST $bl))>>] -> ["Conditional " $tac [1 1] "Rewrite " $C (WITHBINDING ($LIST $bl)) [1 1] "in " $h]
| condrewriterlin [<<(CondRewriteRLin (TACTIC $tac) $h $C ($LIST $bl))>>] -> ["Conditional "  $tac [1 1] "Rewrite <- " $C (WITHBINDING ($LIST $bl)) [1 1] "in " $h]


| DRewriteLR [<<(SubstHypInConcl_LR $id)>>] -> ["Dependent Rewrite -> " $id]
| DRewriteRL [<<(SubstHypInConcl_RL $id)>>] -> ["Dependent Rewrite <- " $id]

| cutrewriteLR [<<(SubstConcl_LR $eqn)>>] -> ["CutRewrite -> " $eqn]
| cutrewriteLRin [<<(SubstHyp_LR $eqn $id)>>]
     -> ["CutRewrite -> " $eqn:E [1 1]"in " $id]

| cutrewriteRL [<<(SubstConcl_RL $eqn)>>] -> ["CutRewrite <- " $eqn:E]
| cutrewriteRLin [<<(SubstHyp_RL $eqn $id)>>]
      -> ["CutRewrite <- " $eqn:E [1 1]"in " $id].
