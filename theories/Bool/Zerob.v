
(* $Id$ *)

Require Arith.
Require Bool.

Definition zerob : nat->bool 
      := [n:nat]Cases n of O => true | (S _) => false end.

Lemma zerob_true_intro : (n:nat)(n=O)->(zerob n)=true.
Destruct n; [Trivial with bool | Intros p H; Inversion H].
Save.
Hints Resolve zerob_true_intro : bool.

Lemma zerob_true_elim : (n:nat)(zerob n)=true->(n=O).
Destruct n; [Trivial with bool | Intros p H; Inversion H].
Save.

Lemma zerob_false_intro : (n:nat)~(n=O)->(zerob n)=false.
Destruct n; [Destruct 1; Auto with bool | Trivial with bool].
Save.
Hints Resolve zerob_false_intro : bool.

Lemma zerob_false_elim : (n:nat)(zerob n)=false->~(n=O).
Destruct n; [Intro H; Inversion H | Auto with bool].
Save.
