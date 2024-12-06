From Stdlib Require Import Lia.
From Stdlib Require Import NArith.
Open Scope N_scope.

Goal forall (a b c: N),
    a <> 0 ->
    c <> 0 ->
    a * ((b + 1) * c) <> 0.
Proof.
  intros. nia.
Qed.
