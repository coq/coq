Require Import ssreflect.

Axiom odd : nat -> Prop.

Lemma simple :
  forall x, 3 <= x -> forall y, odd (y+x) -> x = y -> True.
Proof.
move=> >x_ge_3 >xy_odd.
lazymatch goal with
| |- ?x = ?y -> True => done
end.
Qed.


Definition stuff x := 3 <= x -> forall y, odd (y+x) -> x = y -> True.

Lemma harder : forall x, stuff x.
Proof.
move=> >x_ge_3 >xy_odd.
lazymatch goal with
| |- ?x = ?y -> True => done
end.
Qed.

Lemma homotop : forall x : nat, forall e : x = x, e = e -> True.
Proof.
move=> >eq_ee.
lazymatch goal with
| |- True => done
end.
Qed.
