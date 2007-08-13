Require Import Minus.

Require Export NPlus.
Require Export NDepRec.
Require Export NTimesOrder.
Require Export NMinus.
Require Export NMiscFunct.

(* First we define the functions that will be suppled as
implementations. The parameters in module types, to which these
functions are going to be assigned, are declared Inline,
so in the properties functors the definitions are going to
be unfolded and the theorems proved in these functors
will contain these functions in their statements. *)

(* Decidable equality *)
Fixpoint e (x y : nat) {struct x} : bool :=
match x, y with
| 0, 0 => true
| S x', S y' => e x' y'
| _, _ => false
end.

(* The boolean < function can be defined as follows using the
standard library:

fun n m => proj1_sig (nat_lt_ge_bool n m)

However, this definition seems too complex. First, there are many
functions involved: nat_lt_ge_bool is defined (in Coq.Arith.Bool_nat)
using bool_of_sumbool and

lt_ge_dec : forall x y : nat, {x < y} + {x >= y},

where the latter function is defined using sumbool_not and

le_lt_dec : forall n m : nat, {n <= m} + {m < n}.

Second, this definition is not the most efficient, especially since
le_lt_dec is proved using tactics, not by giving the explicit proof
term. *)

Fixpoint lt (n m : nat) {struct n} : bool :=
match n, m with
| _, 0 => false
| 0, S _ => true
| S n', S m' => lt n' m'
end.

Fixpoint le (n m : nat) {struct n} : bool :=
match n, m with
| 0, _ => true
| S n', S m' => le n' m'
| S _, 0 => false
end.

Delimit Scope NatScope with Nat.
Open Scope NatScope.

(* Domain *)

Module Export NPeanoDomain <: NDomainEqSignature.

Definition N := nat.
Definition E := (@eq nat).
Definition e := e.

Theorem E_equiv_e : forall x y : N, E x y <-> e x y.
Proof.
induction x; destruct y; simpl; try now split; intro.
rewrite <- IHx; split; intro H; [now injection H | now rewrite H].
Qed.

Definition E_equiv : equiv N E := eq_equiv N.

Add Relation N E
 reflexivity proved by (proj1 E_equiv)
 symmetry proved by (proj2 (proj2 E_equiv))
 transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.

End NPeanoDomain.

Module Export PeanoNat <: NatSignature.
Module (*Import*) NDomainModule := NPeanoDomain.

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

Module Export NPeanoDepRec <: NDepRecSignature.
Module Import NDomainModule := NPeanoDomain.
Module Import NatModule := PeanoNat.

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

Module Export NPeanoOrder <: NOrderSignature.
Module Import NatModule := PeanoNat.

Definition lt := lt.
Definition le := le.

Add Morphism lt with signature E ==> E ==> eq_bool as lt_wd.
Proof.
unfold E, eq_bool; congruence.
Qed.

Add Morphism le with signature E ==> E ==> eq_bool as le_wd.
Proof.
unfold E, eq_bool; congruence.
Qed.

(* It would be easier to prove the boolean lemma first because
|| is simplified by simpl unlike \/ *)
Lemma le_lt_bool : forall x y, le x y = (lt x y) || (e x y).
Proof.
induction x as [| x IH]; destruct y; simpl; (reflexivity || apply IH).
Qed.

Theorem le_lt : forall x y, le x y <-> lt x y \/ x = y.
Proof.
intros; rewrite E_equiv_e; rewrite <- eq_true_or;
rewrite <- eq_true_iff; apply le_lt_bool.
Qed.

Theorem lt_0 : forall x, ~ (lt x 0).
Proof.
destruct x as [|x]; simpl; now intro.
Qed.

Lemma lt_S_bool : forall x y, lt x (S y) = le x y.
Proof.
unfold lt, le; induction x as [| x IH]; destruct y as [| y];
simpl; try reflexivity.
destruct x; now simpl.
apply IH.
Qed.

Theorem lt_S : forall x y, lt x (S y) <-> le x y.
Proof.
intros; rewrite <- eq_true_iff; apply lt_S_bool.
Qed.

End NPeanoOrder.

Module Export NPeanoPlus <: NPlusSignature.
Module (*Import*) NatModule := PeanoNat.

Definition plus := plus.

Notation "x + y" := (plus x y) : NatScope.

Add Morphism plus with signature E ==> E ==> E as plus_wd.
Proof.
unfold E; congruence.
Qed.

Theorem plus_0_l : forall n, 0 + n = n.
Proof.
reflexivity.
Qed.

Theorem plus_S_l : forall n m, (S n) + m = S (n + m).
Proof.
reflexivity.
Qed.

End NPeanoPlus.

Module Export NPeanoTimes <: NTimesSignature.
Module Import NPlusModule := NPeanoPlus.

Definition times := mult.

Add Morphism times with signature E ==> E ==> E as times_wd.
Proof.
unfold E; congruence.
Qed.

Theorem times_0_r : forall n, n * 0 = 0.
Proof.
auto.
Qed.

Theorem times_S_r : forall n m, n * (S m) = n * m + n.
Proof.
auto.
Qed.

End NPeanoTimes.

Module Export NPeanoPred <: NPredSignature.
Module Export NatModule := PeanoNat.

Definition P (n : nat) :=
match n with
| 0 => 0
| S n' => n'
end.

Add Morphism P with signature E ==> E as P_wd.
Proof.
unfold E; congruence.
Qed.

Theorem P_0 : P 0 = 0.
Proof.
reflexivity.
Qed.

Theorem P_S : forall n, P (S n) = n.
Proof.
now intro.
Qed.

End NPeanoPred.

Module Export NPeanoMinus <: NMinusSignature.
Module Import NPredModule := NPeanoPred.

Definition minus := minus.

Add Morphism minus with signature E ==> E ==> E as minus_wd.
Proof.
unfold E; congruence.
Qed.

Theorem minus_0_r : forall n, n - 0 = n.
Proof.
now destruct n.
Qed.

Theorem minus_S_r : forall n m, n - (S m) = P (n - m).
Proof.
induction n as [| n IH]; simpl.
now intro.
destruct m; simpl; [apply minus_0_r | apply IH].
Qed.

End NPeanoMinus.

(* Obtaining properties for +, *, <, and their combinations *)

Module Export NPeanoTimesOrderProperties := NTimesOrderProperties NPeanoTimes NPeanoOrder.
Module Export NPeanoDepRecTimesProperties :=
  NDepRecTimesProperties NPeanoDepRec NPeanoTimes.
Module Export NPeanoMinusProperties :=
  NMinusProperties NPeanoMinus NPeanoPlus NPeanoOrder.

Module MiscFunctModule := MiscFunctFunctor PeanoNat.
(* The instruction above adds about 0.5M to the size of the .vo file !!! *)

(*Lemma e_implies_E : forall n m, e n m = true -> n = m.
Proof.
intros n m H; rewrite <- eq_true_unfold_pos in H;
now apply <- E_equiv_e.
Qed.

Add Ring SR : semi_ring (decidable e_implies_E).

Goal forall x y : nat, x + y = y + x. intros. ring.*)
