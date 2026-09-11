Goal forall n, n = n + 0 + 0.
Proof.
  intro n.
  etransitivity (_ + _).
  - apply plus_n_O.
  - apply plus_n_O.
Qed.

From Corelib Require Import RelationClasses.

Lemma and_True_l P : True /\ P <-> P.
Proof. split; intro H; auto. apply H. Qed.

Goal forall P, True /\ True /\ P <-> P.
Proof.
  intro P.
  setoid_etransitivity (_ /\ _).
  - apply and_True_l.
  - apply and_True_l.
Qed.

From Ltac2 Require Import Ltac2.

Goal forall n, n = n + 0 + 0.
Proof.
  intro n.
  etransitivity (_ + _).
  - apply plus_n_O.
  - apply plus_n_O.
Qed.

Goal forall P, True /\ True /\ P <-> P.
Proof.
  intro P.
  (* Future when setoid_etransitivity is bound in ltac2 *)
  ltac1:(setoid_etransitivity (_ /\ _)).
  - apply and_True_l.
  - apply and_True_l.
Qed.
