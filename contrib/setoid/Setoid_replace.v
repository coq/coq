(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$: *)

Declare ML Module "setoid_replace".

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
| new_morphism [ "New" "Morphism" identarg($s) constrarg($m) "." ] -> [(NamedNewMorphism $s $m)]
| new_morphism [ "New" "Morphism" identarg($m) "." ] -> [(NewMorphism $m)]
.

Section Setoid.

Variable A : Type.
Variable Aeq : A -> A -> Prop.

Record Setoid_Theory : Prop :=
{ Seq_refl : (x:A) (Aeq x x);
  Seq_sym : (x,y:A) (Aeq x y) -> (Aeq y x);
  Seq_trans : (x,y,z:A) (Aeq x y) -> (Aeq y z) -> (Aeq x z)
}.

End Setoid.

Definition Prop_S : (Setoid_Theory Prop ([x,y:Prop] x<->y)).
Split; Tauto.
Save.

Add Setoid Prop iff Prop_S.

Hint prop_set : setoid := Resolve (Seq_refl Prop iff Prop_S).
Hint prop_set : setoid := Resolve (Seq_sym Prop iff Prop_S).
Hint prop_set : setoid := Resolve (Seq_trans Prop iff Prop_S).

New Morphism or.
Tauto.
Save.

New Morphism and.
Tauto.
Save.

New Morphism not.
Tauto.
Save.

Definition fleche [A,B:Prop] := A -> B.

New Morphism fleche.
Tauto.
Save.

