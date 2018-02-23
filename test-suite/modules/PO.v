Set Implicit Arguments.
Unset Strict Implicit.

Arguments fst : default implicits.
Arguments snd : default implicits.

Module Type PO.
  Parameter T : Set.
  Parameter le : T -> T -> Prop.

  Axiom le_refl : forall x : T, le x x.
  Axiom le_trans : forall x y z : T, le x y -> le y z -> le x z.
  Axiom le_antis : forall x y : T, le x y -> le y x -> x = y.

  Hint Resolve le_refl le_trans le_antis.
End PO.


Module Pair (X: PO) (Y: PO) <: PO.
  Definition T := (X.T * Y.T)%type.
  Definition le p1 p2 := X.le (fst p1) (fst p2) /\ Y.le (snd p1) (snd p2).

  Hint Unfold le.

  Lemma le_refl : forall p : T, le p p.
    info auto.
  Qed.

  Lemma le_trans : forall p1 p2 p3 : T, le p1 p2 -> le p2 p3 -> le p1 p3.
    unfold le;  intuition; info  eauto.
  Qed.

  Lemma le_antis : forall p1 p2 : T, le p1 p2 -> le p2 p1 -> p1 = p2.
    destruct p1.
    destruct p2.
    unfold le.
     intuition.
     cutrewrite (t = t1).
     cutrewrite (t0 = t2).
    reflexivity.

    info auto.

    info auto.
  Qed.

End Pair.



Require Nat.

Module NN := Pair Nat Nat.

Lemma zz_min : forall p : NN.T, NN.le (0, 0) p.
  info auto with arith.
Qed.
