(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
Declare ML Module "autorewrite".

Grammar vernac orient : ast :=
| lr ["->"] -> ["LR"]
| rl ["<-"] -> ["RL"]
| ng [] -> ["LR"]

with vernac : ast :=
| hint_rew_b [ "Hint" "Rewrite" orient($o) "[" ne_constrarg_list($l) "]" "in"
  identarg($b) "."] ->
  [ (HintRewrite $o (CONSTRLIST ($LIST $l)) $b (TACTIC (Idtac))) ]
| hint_rew_t [ "Hint" "Rewrite" orient($o) "[" ne_constrarg_list($l) "]" "in"
  identarg($b) "using" tacarg($t) "." ] ->
  [ (HintRewrite $o (CONSTRLIST ($LIST $l)) $b (TACTIC $t)) ].

Grammar tactic simple_tactic : ast :=
| auto_rew_b [ "AutoRewrite" "[" ne_identarg_list($l) "]" ] ->
  [ (AutoRewrite ($LIST $l)) ]
| auto_rew_t [ "AutoRewrite" "[" ne_identarg_list($l) "]" "using"
  tactic($t) ] -> [ (AutoRewrite (TACTIC $t) ($LIST $l)) ].

Syntax tactic level 0:
| auto_rew_b [<<(AutoRewrite $l)>>] ->
  [ "AutoRewrite" [1 0] "[" [1 0] $l [1 0] "]" ]
| auto_rew_t [<<(AutoRewrite $t $l)>>] ->
  [ "AutoRewrite" [1 0] "[" [1 0] $l [1 0] "]" [1 0] "using" [1 0] $t ].
