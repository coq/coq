
(* $Id$: *)

Declare ML Module "equality".

Grammar vernac orient_rule: Ast :=
   lr ["LR"] -> [ "LR" ]
  |rl ["RL"] -> [ "RL" ]
with rule_list: AstList :=
   single_rlt [ constrarg($com) orient_rule($ort) ] ->
     [ (VERNACARGLIST $com $ort) ]
  |recursive_rlt [ constrarg($com) orient_rule($ort) rule_list($tail)] ->
    [ (VERNACARGLIST $com $ort) ($LIST $tail) ]
with base_list: AstList :=
   single_blt [identarg($rbase) "[" rule_list($rlt) "]"] ->
     [ (VERNACARGLIST $rbase ($LIST $rlt)) ]
  |recursive_blt [identarg($rbase) "[" rule_list($rlt) "]"
    base_list($blt)] ->
    [ (VERNACARGLIST $rbase ($LIST $rlt)) ($LIST $blt) ]
with vernac: Ast :=
   addrule ["HintRewrite" base_list($blt) "."] ->
     [ (HintRewrite ($LIST $blt)) ].

Grammar tactic list_tactics: AstList :=
   single_lt [tactic($tac)] -> [$tac]
  |recursive_lt [tactic($tac) "|" list_tactics($tail)] ->
    [ $tac ($LIST $tail) ]

with step_largs: AstList :=
   nil_step [] -> []
  |solve_step ["with" "Solve"] -> [(REDEXP (SolveStep))]
  |use_step ["with" "Use"] -> [(REDEXP (Use))]
  |all_step ["with" "All"] -> [(REDEXP (All))]

with rest_largs: AstList :=
   nil_rest [] -> []
  |solve_rest ["with" "Solve"] -> [(REDEXP (SolveRest))]
  |cond_rest ["with" "Cond"] -> [(REDEXP (Cond))]

with autorew_largs: AstList :=
   step_arg ["Step" "=" "[" list_tactics($ltac) "]" step_largs($slargs)] ->
    [(REDEXP (Step ($LIST $ltac))) ($LIST $slargs)]
  |rest_arg ["Rest" "=" "[" list_tactics($ltac) "]" rest_largs($llargs)] ->
    [(REDEXP (Rest ($LIST $ltac))) ($LIST $llargs)]
  |depth_arg ["Depth" "=" numarg($dth)] ->
    [(REDEXP (Depth $dth))]

with list_args_autorew: AstList :=
   nil_laa [] -> []
  |recursive_laa [autorew_largs($largs) list_args_autorew($laa)] ->
    [($LIST $largs) ($LIST $laa)]

with hintbase_list: AstList :=
  nil_hintbase [] -> []
| base_by_name [identarg($id) hintbase_list($tail)] -> 
       [ (REDEXP (ByName $id)) ($LIST $tail)]
| explicit_base ["[" hintbase($b) "]" hintbase_list($tail)] -> 
       [(REDEXP (Explicit ($LIST $b))) ($LIST $tail) ]

with hintbase: AstList := 
  onehint_lr [ constrarg($c) "LR" ] -> [(REDEXP (LR $c))]
| onehint_rl  [ constrarg($c) "RL" ] -> [(REDEXP (RL $c))]
| conshint_lr [ constrarg($c) "LR" hintbase($tail)] -> [(REDEXP (LR $c)) ($LIST $tail)]
| conshint_rl [ constrarg($c) "RL" hintbase($tail)] -> [(REDEXP (RL $c)) ($LIST $tail)]

with simple_tactic: Ast := 
 AutoRewrite [ "AutoRewrite" "[" hintbase_list($lbase) "]"
  list_args_autorew($laa)] ->
  [(AutoRewrite (REDEXP (BaseList ($LIST $lbase))) ($LIST $laa))].

Grammar tactic simple_tactic: Ast :=
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
      -> ["CutRewrite <- " $eqn:E [1 1]"in " $id]
|nil_consbase [<<(CONSBASE)>>] -> []
|single_consbase [<<(CONSBASE $tac)>>] -> [[1 0] $tac]
|nil_ortactic [<<(ORTACTIC)>>] -> []
|single_ortactic [<<(ORTACTIC $tac)>>] -> ["|" $tac]
|AutoRewrite [<<(AutoRewrite $id)>>] -> ["AutoRewrite " $id]
|AutoRewriteBaseList [<<(REDEXP (BaseList $ft ($LIST $tl)))>>] ->
  ["[" $ft (CONSBASE ($LIST $tl)) "]"]
|AutoRewriteStep [<<(REDEXP (Step $ft ($LIST $tl)))>>] ->
  [[0 1] "Step=" "[" $ft (ORTACTIC ($LIST $tl)) "]"]
|AutoRewriteRest [<<(REDEXP (Rest $ft ($LIST $tl)))>>] ->
  [[0 1] "Rest=" "[" $ft (ORTACTIC ($LIST $tl)) "]"]
|AutoRewriteSolveStep [<<(REDEXP (SolveStep))>>] -> ["with Solve"]
|AutoRewriteSolveRest [<<(REDEXP (SolveRest))>>] -> ["with Solve"]
|AutoRewriteUse [<<(REDEXP (Use))>>] -> ["with Use"]
|AutoRewriteAll [<<(REDEXP (All))>>] -> ["with All"]
|AutoRewriteCond [<<(REDEXP (Cond))>>] -> ["with Cond"]
|AutoRewriteDepth [<<(REDEXP (Depth $dth))>>] -> [[0 1] "Depth=" $dth]
|AutoRewriteByName [<<(REDEXP (ByName $id))>>] -> [ $id ]
|AutoRewriteExplicit [<<(REDEXP (Explicit $l))>>] -> ["[" $l "]"]
|AutoRewriteLR [<<(REDEXP (LR $c))>>] -> [ $c "LR" ]
|AutoRewriteRL [<<(REDEXP (RL $c))>>] -> [ $c "RL" ]
.
