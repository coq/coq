(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$: *)

Grammar tactic simple_tactic : ast :=
  setoid_replace [ "Setoid_replace" constrarg($c1) "with" constrarg($c2) ] -> [(Setoid_replace $c1 $c2)]
.

Grammar tactic simple_tactic : ast :=
  setoid_rewriteLR [ "Setoid_rewrite" "->" constrarg($c) ] -> [(Setoid_rewriteLR $c)]
| setoid_rewriteRL [ "Setoid_rewrite" "<-" constrarg($c) ] -> [(Setoid_rewriteRL $c)]
| setoid_rewrite [ "Setoid_rewrite" constrarg($c) ] -> [(Setoid_rewriteLR $c)]
.

Syntax tactic level 0 :
  setoid_replace [<<(Setoid_replace  $c1 $c2)>>] -> [[<hov 0>"Setoid_replace " $c1 [1 1] "with " $c2]]
 | setoid_rewritelr [<<(Setoid_rewriteLR  $c)>>] -> ["Setoid_rewrite " $c]
 | setoid_rewriterl [<<(Setoid_rewriteRL  $c)>>] -> ["Setoid_rewrite <- " $c]
.

Grammar vernac vernac : ast :=
  add_setoid [ "Add" "Setoid" constrarg($a) constrarg($aeq) constrarg($t) "." ] 
    -> [(AddSetoid $a $aeq $t)]
| new_morphism [ "Add" "Morphism" constrarg($m) ":" identarg($s) "." ] -> [(NamedNewMorphism $s $m)]
.
