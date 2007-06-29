Require Import NDomain.
Require Import NAxioms.
Require Import NPlus.
Require Import NTimes.
Require Import NLt.
Require Import NPlusLt.
Require Import NTimesLt.

Require Import ZDomain.
Require Import ZAxioms.
Require Import ZPlus.
Require Import ZTimes.
Require Import ZOrder.
Require Import ZPlusOrder.
Require Import ZTimesOrder.

Module NatPairsDomain (Export PlusModule : NPlus.PlusSignature) <:
  ZDomain.DomainSignature.

Module Export PlusPropertiesModule := NPlus.PlusProperties PlusModule.

Definition Z : Set := (N * N)%type.
Definition E (p1 p2 : Z) := (fst p1) + (snd p2) == (fst p2) + (snd p1).
Definition e (p1 p2 : Z) := e ((fst p1) + (snd p2)) ((fst p2) + (snd p1)).

Theorem E_equiv_e : forall x y : Z, E x y <-> e x y.
Proof.
intros x y; unfold E, e; apply E_equiv_e.
Qed.

Theorem E_equiv : equiv Z E.
Proof.
split; [| split]; unfold reflexive, symmetric, transitive, E.
now intro x.
intros x y z H1 H2.
comm_eq N 



assert (H : ((fst x) + (snd y)) + ((fst y) + (snd z)) ==
            ((fst y) + (snd x)) + ((fst z) + (snd y))); [now apply plus_wd |].
assert (H : (fst y) + (snd y) + (fst x) + (snd z) ==
            (fst y) + (snd y) + (snd x) + (fst z)).


