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

Module NatPairsDomain (NPlusModule : NPlus.PlusSignature) <:
  ZDomain.DomainSignature.
Module Export NPlusPropertiesModule := NPlus.PlusProperties NPlusModule.

Definition Z : Set := (N * N)%type.

Definition E (p1 p2 : Z) := ((fst p1) + (snd p2) == (fst p2) + (snd p1))%Nat.
Definition e (p1 p2 : Z) := e ((fst p1) + (snd p2)) ((fst p2) + (snd p1))%Nat.

Theorem E_equiv_e : forall x y : Z, E x y <-> e x y.
Proof.
intros x y; unfold E, e; apply E_equiv_e.
Qed.

Theorem E_equiv : equiv Z E.
Proof.
split; [| split]; unfold reflexive, symmetric, transitive, E.
(* reflexivity *)
now intro.
(* transitivity *)
intros x y z H1 H2.
apply plus_cancel_l with (p := fst y + snd y).
rewrite (plus_shuffle2 (fst y) (snd y) (fst x) (snd z)).
rewrite (plus_shuffle2 (fst y) (snd y) (fst z) (snd x)).
rewrite plus_comm. rewrite (plus_comm (snd y) (fst x)).
rewrite (plus_comm (snd y) (fst z)). now apply plus_wd.
(* symmetry *)
now intros.
Qed.

Add Relation Z E                                                                                 
 reflexivity proved by (proj1 E_equiv)                                                           
 symmetry proved by (proj2 (proj2 E_equiv))                                                      
 transitivity proved by (proj1 (proj2 E_equiv))                                                  
as E_rel.

End NatPairsDomain.


Module NatPairsInt (Export NPlusModule : NPlus.PlusSignature) <: IntSignature.

Module Export ZDomainModule := NatPairsDomain NPlusModule.

Definition O := (0, 0).
Definition S (n : Z) := (NatModule.S (fst n), snd n).
Definition P (n : Z) := (fst n, NatModule.S (snd n)).
(* Unfortunately, we do not have P (S n) = n but only P (S n) == n.
It could be possible to consider as "canonical" only pairs where one of
the elements is 0, and make all operations convert canonical values into
other canonical values. We do not do this because this is more complex
and because we do not have the predecessor function on N at this point. *)

Add Morphism S with signature E ==> E as S_wd.
Proof.
unfold S, E; intros n m H; simpl.
do 2 rewrite plus_Sn_m; now rewrite H.
Qed.

Add Morphism P with signature E ==> E as P_wd.
Proof.
unfold P, E; intros n m H; simpl.
do 2 rewrite plus_n_Sm; now rewrite H.
Qed.

Theorem S_inj : forall x y : Z, S x == S y -> x == y.



Definition N_Z (n : nat) := nat_rec (fun _ : nat => Z) 0 (fun _ p => S p).

