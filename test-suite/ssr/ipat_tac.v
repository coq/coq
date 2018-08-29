Require Import ssreflect.

Ltac fancy := case; last first.

Notation fancy := (ltac:( fancy )).

Ltac replicate n :=
  let what := fresh "_replicate_" in
  move=> what; do n! [ have := what ]; clear what.

Notation replicate n := (ltac:( replicate n )).

Lemma foo x (w : nat) (J : bool -> nat -> nat) : exists y, x=0+y.
Proof.
move: (w) => /ltac:(idtac) _.
move: w => /(replicate 6) w1 w2 w3 w4 w5 w6.
move: w1 => /J/fancy [w'||];last exact: false.
  move: w' => /J/fancy[w''||]; last exact: false.
    by exists x.
  by exists x.
by exists x.
Qed.

Ltac unfld what := rewrite /what.

Notation "% n" := (ltac:( unfld n )) (at level 0) : ssripat_scope.
Notation "% n" := n : nat_scope.

Open Scope nat_scope.


Definition def := 4.

Lemma test : True -> def = 4.
Proof.
move=> _ /(% def).
match goal with |- 4 = 4 => reflexivity end.
Qed.
