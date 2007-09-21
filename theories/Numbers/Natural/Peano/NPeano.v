Require Import Arith.
Require Import NMinus.

Module NPeanoAxiomsMod <: NAxiomsSig.

Definition N := nat.
Definition E := (@eq nat).
Definition O := 0.
Definition S := S.
Definition P := pred.
Definition plus := plus.
Definition minus := minus.
Definition times := mult.
Definition lt := lt.
Definition le := le.
Definition recursion : forall A : Set, A -> (N -> A -> A) -> N -> A :=
  fun A : Set => nat_rec (fun _ => A).
Implicit Arguments recursion [A].

Theorem E_equiv : equiv nat E.
Proof (eq_equiv nat).

Add Relation nat E
 reflexivity proved by (proj1 E_equiv)
 symmetry proved by (proj2 (proj2 E_equiv))
 transitivity proved by (proj1 (proj2 E_equiv))
as E_rel.

(* If we say "Add Relation nat (@eq nat)" instead of "Add Relation nat E"
then the theorem generated for succ_wd below is forall x, succ x = succ x,
which does not match the axioms in NAxiomsSig *)

Add Morphism S with signature E ==> E as succ_wd.
Proof.
congruence.
Qed.

Add Morphism P with signature E ==> E as pred_wd.
Proof.
congruence.
Qed.

Add Morphism plus with signature E ==> E ==> E as plus_wd.
Proof.
congruence.
Qed.

Add Morphism minus with signature E ==> E ==> E as minus_wd.
Proof.
congruence.
Qed.

Add Morphism times with signature E ==> E ==> E as times_wd.
Proof.
congruence.
Qed.

Add Morphism lt with signature E ==> E ==> iff as lt_wd.
Proof.
unfold E; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Add Morphism le with signature E ==> E ==> iff as le_wd.
Proof.
unfold E; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Theorem induction :
  forall A : nat -> Prop, predicate_wd (@eq nat) A ->
    A 0 -> (forall n : nat, A n -> A (S n)) -> forall n : nat, A n.
Proof.
intros; now apply nat_ind.
Qed.

Theorem pred_0 : pred 0 = 0.
Proof.
reflexivity.
Qed.

Theorem pred_succ : forall n : nat, pred (S n) = n.
Proof.
reflexivity.
Qed.

Theorem plus_0_l : forall n : nat, 0 + n = n.
Proof.
reflexivity.
Qed.

Theorem plus_succ_l : forall n m : nat, (S n) + m = S (n + m).
Proof.
reflexivity.
Qed.

Theorem minus_0_r : forall n : nat, n - 0 = n.
Proof.
intro n; now destruct n.
Qed.

Theorem minus_succ_r : forall n m : nat, n - (S m) = pred (n - m).
Proof.
intros n m; induction n m using nat_double_ind; simpl; auto. apply minus_0_r.
Qed.

Theorem times_0_r : forall n : nat, n * 0 = 0.
Proof.
exact mult_0_r.
Qed.

Theorem times_succ_r : forall n m : nat, n * (S m) = n * m + n.
Proof.
intros n m; symmetry; apply mult_n_Sm.
Qed.

Theorem le_lt_or_eq : forall n m : nat, n <= m <-> n < m \/ n = m.
Proof.
intros n m; split.
apply le_lt_or_eq.
intro H; destruct H as [H | H].
now apply lt_le_weak. rewrite H; apply le_refl.
Qed.

Theorem nlt_0_r : forall n : nat, ~ (n < 0).
Proof.
exact lt_n_O.
Qed.

Theorem lt_succ_le : forall n m : nat, n < S m <-> n <= m.
Proof.
intros n m; split; [apply lt_n_Sm_le | apply le_lt_n_Sm].
Qed.

Theorem recursion_wd : forall (A : Set) (EA : relation A),
  forall a a' : A, EA a a' ->
    forall f f' : N -> A -> A, eq_fun2 (@eq nat) EA EA f f' ->
      forall n n' : N, n = n' ->
        EA (recursion a f n) (recursion a' f' n').
Proof.
unfold eq_fun2; induction n; intros n' Enn'; rewrite <- Enn' in *; simpl; auto.
Qed.

Theorem recursion_0 :
  forall (A : Set) (a : A) (f : N -> A -> A), recursion a f 0 = a.
Proof.
reflexivity.
Qed.

Theorem recursion_succ :
  forall (A : Set) (EA : relation A) (a : A) (f : N -> A -> A),
    EA a a -> fun2_wd (@eq nat) EA EA f ->
      forall n : N, EA (recursion a f (S n)) (f n (recursion a f n)).
Proof.
unfold eq_fun2; induction n; simpl; auto.
Qed.

End NPeanoAxiomsMod.

(* Now we apply the largest property functor *)

Module Export NPeanoMinusPropMod := NMinusPropFunct NPeanoAxiomsMod.

(*

Theorem succ_wd : fun_wd (@eq nat) (@eq nat) S.
Proof.
congruence.
Qed.

Theorem succ_inj : forall n1 n2 : nat, S n1 = S n2 -> n1 = n2.
Proof.
intros n1 n2 H; now simplify_eq H.
Qed.

Theorem succ_neq_0 : forall n : nat, S n <> 0.
Proof.
intros n H; simplify_eq H.
Qed.


Definition N := nat.
Definition E := (@eq nat).
Definition O := 0.
Definition S := S.

End NPeanoBaseMod.

Module NPeanoPlusMod <: NPlusSig.
Module NBaseMod := NPeanoBaseMod.

Theorem plus_wd : fun2_wd (@eq nat) (@eq nat) (@eq nat) plus.
Proof.
congruence.
Qed.

Theorem plus_0_l : forall n, 0 + n = n.
Proof.
reflexivity.
Qed.

Theorem plus_succ_l : forall n m, (S n) + m = S (n + m).
Proof.
reflexivity.
Qed.

Definition plus := plus.

End NPeanoPlusMod.

Module Export NPeanoBasePropMod := NBasePropFunct NPeanoBaseMod.
Module Export NPeanoPlusPropMod := NPlusPropFunct NPeanoPlusMod.


Module Export NPeanoDepRec <: NDepRecSignature.
Module Import NDomainModule := NPeanoDomain.
Module Import NBaseMod := PeanoNat.

Definition dep_recursion := nat_rec.

Theorem dep_recursion_0 :
  forall (A : N -> Set) (a : A 0) (f : forall n, A n -> A (S n)),
    dep_recursion A a f 0 = a.
Proof.
reflexivity.
Qed.

Theorem dep_recursion_succ :
  forall (A : N -> Set) (a : A 0) (f : forall n, A n -> A (S n)) (n : N),
    dep_recursion A a f (S n) = f n (dep_recursion A a f n).
Proof.
reflexivity.
Qed.

End NPeanoDepRec.

Module Export NPeanoOrder <: NOrderSig.
Module Import NBaseMod := PeanoNat.

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

Lemma lt_succ_bool : forall x y, lt x (S y) = le x y.
Proof.
unfold lt, le; induction x as [| x IH]; destruct y as [| y];
simpl; try reflexivity.
destruct x; now simpl.
apply IH.
Qed.

Theorem lt_succ : forall x y, lt x (S y) <-> le x y.
Proof.
intros; rewrite <- eq_true_iff; apply lt_succ_bool.
Qed.

End NPeanoOrder.

Module Export NPeanoTimes <: NTimesSig.
Module Import NPlusMod := NPeanoPlus.

Definition times := mult.

Add Morphism times with signature E ==> E ==> E as times_wd.
Proof.
unfold E; congruence.
Qed.

Theorem times_0_r : forall n, n * 0 = 0.
Proof.
auto.
Qed.

Theorem times_succ_r : forall n m, n * (S m) = n * m + n.
Proof.
auto.
Qed.

End NPeanoTimes.

Module Export NPeanoPred <: NPredSignature.
Module Export NBaseMod := PeanoNat.

Definition P (n : nat) :=
match n with
| 0 => 0
| S n' => n'
end.

Add Morphism P with signature E ==> E as pred_wd.
Proof.
unfold E; congruence.
Qed.

Theorem pred_0 : P 0 = 0.
Proof.
reflexivity.
Qed.

Theorem pred_succ : forall n, P (S n) = n.
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

Theorem minus_succ_r : forall n m, n - (S m) = P (n - m).
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

Theorem E_equiv_e : forall x y : N, E x y <-> e x y.
Proof.
induction x; destruct y; simpl; try now split; intro.
rewrite <- IHx; split; intro H; [now injection H | now rewrite H].
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

Theorem recursion_succ :
forall (A : Set) (EA : relation A) (a : A) (f : N -> A -> A),
  EA a a -> fun2_wd E EA EA f ->
    forall n : N, EA (recursion a f (S n)) (f n (recursion a f n)).
Proof.
intros A EA a f EAaa f_wd. unfold fun2_wd, E in *.
induction n; simpl; now apply f_wd.
Qed.

(*Lemma e_implies_E : forall n m, e n m = true -> n = m.
Proof.
intros n m H; rewrite <- eq_true_unfold_pos in H;
now apply <- E_equiv_e.
Qed.

Add Ring SR : semi_ring (decidable e_implies_E).

Goal forall x y : nat, x + y = y + x. intros. ring.*)
*)


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
