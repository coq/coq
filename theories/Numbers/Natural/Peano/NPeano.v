Require Export NDepRec.
Require Export NTimesOrder.
Require Export NMinus.
Require Export NMiscFunct.

Module NPeanoDomain <: NDomainEqSignature.
(*  with Definition N := nat
  with Definition E := (@eq nat)
  with Definition e := eq_nat_bool.*)

Delimit Scope NatScope with Nat.

Definition N := nat.
Definition E := (@eq nat).
Definition e := eq_nat_bool.

Theorem E_equiv_e : forall x y : N, E x y <-> e x y.
Proof.
unfold E, e; intros x y; split; intro H;
[rewrite H; apply eq_nat_bool_refl |
now apply eq_nat_bool_implies_eq].
Qed.

Definition E_equiv : equiv N E := eq_equiv N.

Add Relation N E
 reflexivity proved by (proj1 E_equiv)
 symmetry proved by (proj2 (proj2 E_equiv))
 transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.

End NPeanoDomain.

Module PeanoNat <: NatSignature.
Module Export NDomainModule := NPeanoDomain.

Definition O := 0.
Definition S := S.

Add Morphism S with signature E ==> E as S_wd.
Proof.
congruence.
Qed.

Theorem induction :
  forall P : nat -> Prop, pred_wd (@eq nat) P ->
    P 0 -> (forall n, P n -> P (S n)) -> forall n, P n.
Proof.
intros P W Base Step n; elim n; assumption.
Qed.

Definition recursion := fun A : Set => nat_rec (fun _ => A).
Implicit Arguments recursion [A].

Theorem recursion_wd :
forall (A : Set) (EA : relation A),
  forall a a' : A, EA a a' ->
    forall f f' : N -> A -> A, eq_fun2 E EA EA f f' ->
      forall x x' : N, x = x' ->
        EA (recursion a f x) (recursion a' f' x').
Proof.
unfold fun2_wd, E.
intros A EA a a' Eaa' f f' Eff'.
induction x as [| n IH]; intros x' H; rewrite <- H; simpl.
assumption.
apply Eff'; [reflexivity | now apply IH].
Qed.

Theorem recursion_0 :
  forall (A : Set) (a : A) (f : N -> A -> A), recursion a f O = a.
Proof.
reflexivity.
Qed.

Theorem recursion_S :
forall (A : Set) (EA : relation A) (a : A) (f : N -> A -> A),
  EA a a -> fun2_wd E EA EA f ->
    forall n : N, EA (recursion a f (S n)) (f n (recursion a f n)).
Proof.
intros A EA a f EAaa f_wd. unfold fun2_wd, E in *.
induction n; simpl; now apply f_wd.
Qed.

End PeanoNat.

Module NPeanoDepRec <: NDepRecSignature.

Module Export NDomainModule := NPeanoDomain.
Module Export NatModule <: NatSignature := PeanoNat.

Definition dep_recursion := nat_rec.

Theorem dep_recursion_0 :
  forall (A : N -> Set) (a : A 0) (f : forall n, A n -> A (S n)),
    dep_recursion A a f 0 = a.
Proof.
reflexivity.
Qed.

Theorem dep_recursion_S :
  forall (A : N -> Set) (a : A 0) (f : forall n, A n -> A (S n)) (n : N),
    dep_recursion A a f (S n) = f n (dep_recursion A a f n).
Proof.
reflexivity.
Qed.

End NPeanoDepRec.

Module NPeanoPlus <: NPlusSignature.
Module Export NatModule := PeanoNat.

Definition plus := plus.

Add Morphism plus with signature E ==> E ==> E as plus_wd.
Proof.
unfold E; congruence.
Qed.

Theorem plus_0_n : forall n, 0 + n = n.
Proof.
reflexivity.
Qed.

Theorem plus_Sn_m : forall n m, (S n) + m = S (n + m).
Proof.
reflexivity.
Qed.

End NPeanoPlus.

Module NPeanoTimes <: NTimesSignature.
Module Export NPlusModule := NPeanoPlus.

Definition times := mult.

Add Morphism times with signature E ==> E ==> E as times_wd.
Proof.
unfold E; congruence.
Qed.

Theorem times_0_n : forall n, 0 * n = 0.
Proof.
auto.
Qed.

Theorem times_Sn_m : forall n m, (S n) * m = m + n * m.
Proof.
auto.
Qed.

End NPeanoTimes.

Module NPeanoLt <: NLtSignature.
Module Export NatModule := PeanoNat.

Definition lt := lt_bool.

Add Morphism lt with signature E ==> E ==> eq_bool as lt_wd.
Proof.
unfold E, eq_bool; congruence.
Qed.

Theorem lt_0 : forall x, ~ (lt x 0).
Proof.
exact lt_bool_0.
Qed.

Theorem lt_S : forall x y, lt x (S y) <-> lt x y \/ x = y.
Proof.
exact lt_bool_S.
Qed.

End NPeanoLt.

Module NPeanoPred <: NPredSignature.

(* Obtaining properties for +, *, <, and their combinations *)

Module Export NPeanoTimesLtProperties := NTimesLtProperties NPeanoTimes NPeanoLt.
Module Export NPeanoDepRecTimesProperties :=
  NDepRecTimesProperties NPeanoDepRec NPeanoTimes.

Module MiscFunctModule := MiscFunctFunctor PeanoNat.
(* The instruction above adds about 0.5M to the size of the .vo file !!! *)
