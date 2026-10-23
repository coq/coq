From Corelib Require Import ssreflect.
Set Universe Polymorphism.
Axiom foo@{i} : nat.
Set Printing Universes.

Axiom lemma@{i} : foo@{i} = 0. 

Monomorphic Universes i j.
Monomorphic Constraint i < j.

Lemma works : foo@{i} = foo@{j}.
Proof.
  (* This separately rewrites each foo@{_} call, no issue *)
  rewrite !{1}lemma. reflexivity.
Qed.
Lemma test : foo@{i} = foo@{j}.
Proof.
  (* This can only capture a single foo@{_} call *)
  rewrite lemma.
  Fail reflexivity.
Abort.
