Require Import ssreflect ssrbool.

 Axiom eqn : nat -> nat -> bool.
 Infix "==" := eqn (at level 40).
 Axiom eqP : forall x y : nat, reflect (x = y) (x == y).

 Lemma test1 :
   forall x y : nat, x = y -> forall z : nat, y == z -> x = z.
 Proof.
 by move=> x y + z /eqP <-; apply.
 Qed.

 Lemma test2 : forall (x y : nat) (e : x = y), e = e -> x = y.
 Proof.
 move=> + y + _ => x def_x; exact: (def_x : x = y).
 Qed.

 Lemma test3 :
   forall x y : nat, x = y -> forall z : nat, y == z -> x = z.
 Proof.
 move=> ++++ /eqP <- => x y e z; exact: e.
 Qed.
