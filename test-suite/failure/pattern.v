(* Check that untypable beta-expansion are trapped *)

Variable A:nat->Type.
Variable n:nat.
Variable P : (m:nat)m=n->Prop.

Goal (p:n=n)(P n p).
Intro.
Pattern n p. (* Non typable generalization *)
