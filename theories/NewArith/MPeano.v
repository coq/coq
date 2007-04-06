Require Import Arith.
Require Import Axioms.
Require Import Plus.
Require Import Times.
Require Import Lt.
Require Import PlusLt.
Require Import TimesLt.
Require Import MiscFunct.

Inductive mnat : Set :=
| mZ : mnat
| mS : mnat -> mnat
| mO : mnat -> mnat.

Notation "0" := mZ : mnat_scope.
Open Scope mnat_scope.

Fixpoint mnat_to_nat (x : mnat) : nat :=
match x with
| mZ => 0%nat
| mS x' => S (mnat_to_nat x')
| mO x' => mnat_to_nat x'
end.

Fixpoint nat_to_mnat (x : nat) : mnat :=
match x with
| O => mZ
| S x' => mS (mO (nat_to_mnat x'))
end.

Definition eq_mnat_bool (x y : mnat) : bool :=
  eq_nat_bool (mnat_to_nat x) (mnat_to_nat y).

Definition eq_mnat (x y : mnat) : Prop :=
  eq_true (eq_mnat_bool x y).

Notation "x == y" := (eq_mnat x y) (at level 70) : mnat_scope.

Theorem eq_mnat_refl : reflexive mnat eq_mnat.
Proof.
intro x; unfold reflexive, eq_mnat, eq_mnat_bool; apply eq_nat_bool_refl.
Qed.

Theorem eq_mnat_symm : symmetric mnat eq_mnat.
Proof.
unfold symmetric, eq_mnat, eq_mnat_bool.
intros x y H; apply eq_nat_bool_implies_eq in H; rewrite H; apply eq_nat_bool_refl.
Qed.

Theorem eq_mnat_trans : transitive mnat eq_mnat.
Proof.
unfold transitive, eq_mnat, eq_mnat_bool.
intros x y z H1 H2.
apply eq_nat_bool_implies_eq in H1; apply eq_nat_bool_implies_eq in H2.
rewrite H1; rewrite H2. apply eq_nat_bool_refl.
Qed.

Add Relation mnat eq_mnat
reflexivity proved by eq_mnat_refl
symmetry proved by eq_mnat_symm
transitivity proved by eq_mnat_trans
as eq_mnar_rel.

(* We need to declare mnat_to_nat as a morphism to be able to rewrite
(mnat_to_nat x) to (mnat_to_nat x') whenever x == x'. This will be
useful when we declare operation on mnat in terms of operations on
nat, using mnat_to_nat, and we eould like to prove that they are
well-defined. *)

Add Morphism mnat_to_nat with signature eq_mnat ==> (@eq nat)
as mnat_to_nat_wd.
Proof.
intros m n Emn; now apply eq_nat_bool_implies_eq.
Qed.

(* The converse function, nat_to_mnat, is a morphism because it is
defined on nat with Leibnitz equality *)

Theorem mOx_x : forall x y, mO x == y -> x == y.
Proof.
intros x y H; unfold eq_mnat, eq_mnat_bool in H; simpl in H. assumption.
Qed.

Theorem x_mOx : forall x, x == mO x.
Proof.
intros x; unfold eq_mnat, eq_mnat_bool; simpl; apply eq_nat_bool_refl.
Qed.

Theorem mS_0 : forall x, ~ (mS x == 0).
Proof.
unfold eq_mnat, eq_mnat_bool. simpl. unfold not; now intros.
Qed.

Add Morphism mS with signature eq_mnat ==> eq_mnat as mS_wd.
Proof.
unfold eq_mnat, eq_mnat_bool; simpl. trivial.
Qed.

Add Morphism mO with signature eq_mnat ==> eq_mnat as mO_wd.
Proof.
intros m n H; now do 2 rewrite <- x_mOx.
Qed.

Theorem mnat_conversions_inverse1 :
  forall n : mnat, nat_to_mnat (mnat_to_nat n) == n.
Proof.
induction n as [| n IH | n IH]; simpl.
reflexivity.
rewrite IH. unfold eq_mnat, eq_mnat_bool; simpl. apply eq_nat_bool_refl.
rewrite IH. apply x_mOx.
Qed.

Theorem mnat_conversions_inverse2 :
  forall n : nat, mnat_to_nat (nat_to_mnat n) = n.
Proof.
induction n as [| n IH]; simpl.
reflexivity.
now rewrite IH.
Qed.

Section MNatRecursion.

Variable A : Set.
Variable a : A.
Variable f : mnat -> A -> A.
Variable EA : relation A.

Fixpoint mnat_recursion (x : mnat) :=
match x with
| mZ => a
| mS x' => f x' (mnat_recursion x')
| mO x' => (mnat_recursion x')
end.

Lemma mnat_rec_0 : forall x, x == mZ -> mnat_recursion x = a.
Proof.
induction x; simpl.
trivial.
unfold eq_mnat, eq_mnat_bool; simpl; now intro.
intro H; apply IHx; now apply mOx_x.
Qed.

End MNatRecursion.

Implicit Arguments mnat_recursion [A].

Module MPeanoDomain <: DomainSignature.

Definition N := mnat.
Definition E : relation mnat := eq_mnat.
Definition e := eq_mnat_bool.

Theorem E_equiv_e : forall x y : N, E x y <-> e x y.
Proof.
unfold E, e, eq_mnat; reflexivity.
Qed.

Theorem E_equiv : equiv mnat eq_mnat.
Proof.
unfold equiv; split;
[exact eq_mnat_refl | split; [exact eq_mnat_trans | exact eq_mnat_symm]].
Qed.

Add Relation N E
 reflexivity proved by (proj1 E_equiv)
 symmetry proved by (proj2 (proj2 E_equiv))
 transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.

End MPeanoDomain.

Module MPeanoNat <: NatSignature.

Module Export DomainModule := MPeanoDomain.

Definition O := mZ.
Definition S := mS.

Add Morphism S with signature E ==> E as S_wd.
Proof.
exact mS_wd.
Qed.

Theorem induction :
  forall P : mnat -> Prop, pred_wd eq_mnat P ->
    P mZ -> (forall n, P n -> P (mS n)) -> forall n, P n.
Proof.
intros P P_wd P0 PS.
induction n.
assumption.
apply PS; assumption.
unfold pred_wd in P_wd.
assert (H : n == mO n); [apply x_mOx|].
apply P_wd in H. now apply (proj1 H).
Qed.

Definition recursion := mnat_recursion.
Implicit Arguments recursion [A].

Theorem recursion_wd :
forall (A : Set) (EA : relation A),
  forall a a' : A, EA a a' ->
    forall f f' : mnat -> A -> A, eq_fun2 eq_mnat EA EA f f' ->
      forall x x' : mnat, x == x' ->
        EA (mnat_recursion a f x) (mnat_recursion a' f' x').
Proof.
intros A EA a a' EAaa' f f' Eff'.
induction x; simpl.
intros. now rewrite mnat_rec_0.
induction x'; simpl.
unfold eq_mnat, eq_mnat_bool; simpl; now intro.
unfold eq_mnat, eq_mnat_bool; simpl; intro H.
apply Eff'.
assumption. apply IHx; assumption.
intro H. symmetry in H. apply mOx_x in H. symmetry in H. now apply IHx'.
intros x' H; apply mOx_x in H. now apply IHx.
Qed.

Theorem recursion_0 :
  forall (A : Set) (a : A) (f : mnat -> A -> A),
    mnat_recursion a f mZ = a.
Proof.
reflexivity.
Qed.

Theorem recursion_S :
forall (A : Set) (EA : relation A) (a : A) (f : mnat -> A -> A),
  EA a a -> fun2_wd eq_mnat EA EA f ->
    forall n : mnat, EA (mnat_recursion a f (mS n)) (f n (mnat_recursion a f n)).
Proof.
intros A EA a f EAaa f_wd. unfold fun2_wd in f_wd.
induction n as [| n IH | n IH]; simpl in *; apply f_wd; try (reflexivity || assumption).
now apply recursion_wd with (EA := EA).
Qed.

End MPeanoNat.

(*Module Import MPeanoRecursionExamples := RecursionExamples MPeanoNat.

Eval compute in mnat_to_nat (log 12).

Eval compute in mnat_to_nat (mult 3 5).*)

Definition mnat_plus (m n : mnat) : mnat :=
  nat_to_mnat ((mnat_to_nat m) + (mnat_to_nat n))%nat.

Notation "x + y" := (mnat_plus x y) : mnat_scope.

Add Morphism mnat_plus
with signature eq_mnat ==> eq_mnat ==> eq_mnat
as mnat_plus_wd.
Proof.
intros x x' Exx' y y' Eyy'.
unfold mnat_plus.
now rewrite Exx'; rewrite Eyy'.
Qed.

Module MPeanoPlus <: PlusSignature.

Module Export NatModule := MPeanoNat.

Definition plus := mnat_plus.

Add Morphism plus with signature E ==> E ==> E as plus_wd.
Proof.
exact mnat_plus_wd.
Qed.

Theorem plus_0_n : forall n, 0 + n == n.
Proof.
intro n; unfold mnat_plus; simpl. apply mnat_conversions_inverse1.
Qed.

Theorem plus_Sn_m : forall n m, (mS n) + m == mS (n + m).
Proof.
intros n m; unfold mnat_plus; simpl.
apply S_wd. symmetry; apply x_mOx.
Qed.

End MPeanoPlus.

Definition mnat_times (m n : mnat) : mnat :=
  nat_to_mnat ((mnat_to_nat m) * (mnat_to_nat n))%nat.

Notation "x * y" := (mnat_times x y) : mnat_scope.

Add Morphism mnat_times
with signature eq_mnat ==> eq_mnat ==> eq_mnat
as mnat_times_wd.
Proof.
unfold mnat_times.
intros x x' Exx' y y' Eyy'.
now rewrite Exx'; rewrite Eyy'.
Qed.

Module MPeanoTimes <: TimesSignature.
Module Export PlusModule := MPeanoPlus.

Definition times := mnat_times.

Add Morphism times with signature E ==> E ==> E as times_wd.
Proof.
exact mnat_times_wd.
Qed.

Theorem times_0_n : forall n, 0 * n == 0.
Proof.
intro n; unfold mnat_times; now simpl.
Qed.

Theorem times_Sn_m : forall n m, (S n) * m == m + n * m.
Proof.
intros n m; unfold mnat_times, mnat_plus; simpl.
now rewrite mnat_conversions_inverse2.
Qed.

End MPeanoTimes.

Definition mnat_lt (m n : mnat) : bool :=
  lt_bool (mnat_to_nat m) (mnat_to_nat n).

Notation "x < y" := (eq_true (mnat_lt x y)) : mnat_scope.

Add Morphism mnat_lt
with signature eq_mnat ==> eq_mnat ==> eq_bool
as mnat_lt_wd.
Proof.
unfold eq_bool, mnat_lt.
intros x x' Exx' y y' Eyy'.
rewrite Exx'; now rewrite Eyy'.
Qed.

Module MPeanoLt <: LtSignature.
Module Export NatModule := MPeanoNat.

Definition lt := mnat_lt.

Add Morphism lt with signature E ==> E ==> eq_bool as lt_wd.
Proof.
exact mnat_lt_wd.
Qed.

Theorem lt_0 : forall n, ~ (n < 0).
Proof.
intro n; unfold mnat_lt; simpl. apply lt_bool_0.
Qed.

Theorem lt_S : forall m n, m < (S n) <-> m < n \/ m == n.
Proof.
intros m n; unfold mnat_lt; simpl.
assert (H : m == n <-> mnat_to_nat m = mnat_to_nat n);
[unfold eq_mnat, eq_mnat_bool; split;
[now apply eq_nat_bool_implies_eq |
intro H; rewrite H; apply eq_nat_bool_refl] |].
rewrite H. apply lt_bool_S.
Qed.

End MPeanoLt.

(* Obtaining properties for +, *, <, and their combinations *)

Module Export MPeanoPlusProperties := PlusProperties MPeanoPlus.
Module Export MPeanoTimesProperties := TimesProperties MPeanoTimes.
Module Export MPeanoLtProperties := LtProperties MPeanoLt.
Module Export MPeanoPlusLtProperties := PlusLtProperties MPeanoPlus MPeanoLt.
Module Export MPeanoTimesLtProperties := TimesLtProperties MPeanoTimes MPeanoLt.

Module MiscFunctModule := MiscFunctFunctor MPeanoNat.

(* Below is an attempt to prove alternative axioms for recursion from OtherInd.v.
It is not clear whether this is easier. *)

Theorem rec_0 :
  forall (A : Set) (EA : relation A) (a : A) (f : N -> A -> A),
    EA a a -> forall x : N, x == 0 -> EA (recursion a f x) a.
Proof.
intros A EA a f H.
induction x as [| x IH | x IH]; simpl.
now intro.
intro H1; false_hyp H1 mS_0.
intro H1; apply mOx_x in H1; now apply IH in H1.
Qed.

Lemma rec_wd_n :
  forall (A : Set) (EA : relation A) (a : A) (f : N -> A -> A),
    EA a a -> fun2_wd E EA EA f ->
      forall n m : N, n == m -> EA (recursion a f n) (recursion a f m).
Proof.
intros A EA a f Eaa f_wd.
induction n; induction m; simpl in *.
now intro.
intro H; symmetry in H; false_hyp H mS_0.
apply IHm; now rewrite x_mOx.
intro H; false_hyp H mS_0.
intro H; apply f_wd. now apply S_inj. apply IHn. now apply S_inj.
intro H; rewrite <- x_mOx in H. now apply IHm.
intro H; rewrite <- x_mOx in H. now apply (IHn 0).
intro H; rewrite <- x_mOx in H. now apply (IHn (S m)). (* Does not work with apply IHn *)
intro H; apply IHn; now do 2 rewrite <- x_mOx in H.
Qed.

Theorem rec_S :
  forall (A : Set) (EA : relation A) (a : A) (f : N -> A -> A),
    EA a a -> fun2_wd E EA EA f ->
      forall n m : N, n == S m -> EA (recursion a f n) (f m (recursion a f m)).
Proof.
intros A EA a f Eaa f_wd.
induction n as [| n IH | n IH]; simpl.
intros m H; symmetry in H; false_hyp H mS_0.
intros m H; apply S_inj in H.
induction m; simpl.
assert (EA (recursion a f n) a). now apply rec_0. now apply f_wd.
apply f_wd. assumption. apply IH. assumption.
apply f_wd. assumption. apply rec_wd_n with (EA := EA). assumption. assumption. now apply mOx_x.
intros m H. apply mOx_x in H. now apply IH.
Qed.

Close Scope mnat_scope.
