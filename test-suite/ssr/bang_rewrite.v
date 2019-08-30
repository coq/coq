Set Universe Polymorphism.

Require Import ssreflect.

Axiom mult@{i} : nat -> nat -> nat.
Notation "m * n" := (mult m n).

Axiom multA : forall a b c, (a * b) * c = a * (b * c).

(* Previously the following gave a universe error: *)

Lemma multAA a b c d : ((a * b) * c) * d = a * (b * (c * d)).
Proof. by rewrite !multA. Qed.
