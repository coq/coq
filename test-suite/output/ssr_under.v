From Coq Require Import ssreflect.

Axiom subnn : forall n : nat, n - n = 0.
Parameter G : (nat -> nat) -> nat -> nat.
Axiom eq_G :
  forall F1 F2 : nat -> nat,
    (forall n : nat, F1 n = F2 n) ->
    forall n : nat, G F1 n = G F2 n.

Ltac show := match goal with [|-?g] => idtac g end.

Lemma example_G (n : nat) : G (fun n => n - n) n >= 0.
under eq_G => m do show; rewrite subnn.
show.
Abort.
