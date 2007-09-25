Require Import Arith.
Require Import NMinus.

Module NPeanoAxiomsMod <: NAxiomsSig.
Module Export NZOrdAxiomsMod <: NZOrdAxiomsSig.
Module Export NZAxiomsMod <: NZAxiomsSig.

Definition NZ := nat.
Definition NZE := (@eq nat).
Definition NZ0 := 0.
Definition NZsucc := S.
Definition NZpred := pred.
Definition NZplus := plus.
Definition NZminus := minus.
Definition NZtimes := mult.

Theorem NZE_equiv : equiv nat NZE.
Proof (eq_equiv nat).

Add Relation nat NZE
 reflexivity proved by (proj1 NZE_equiv)
 symmetry proved by (proj2 (proj2 NZE_equiv))
 transitivity proved by (proj1 (proj2 NZE_equiv))
as NZE_rel.

(* If we say "Add Relation nat (@eq nat)" instead of "Add Relation nat NZE"
then the theorem generated for succ_wd below is forall x, succ x = succ x,
which does not match the axioms in NAxiomsSig *)

Add Morphism NZsucc with signature NZE ==> NZE as NZsucc_wd.
Proof.
congruence.
Qed.

Add Morphism NZpred with signature NZE ==> NZE as NZpred_wd.
Proof.
congruence.
Qed.

Add Morphism NZplus with signature NZE ==> NZE ==> NZE as NZplus_wd.
Proof.
congruence.
Qed.

Add Morphism NZminus with signature NZE ==> NZE ==> NZE as NZminus_wd.
Proof.
congruence.
Qed.

Add Morphism NZtimes with signature NZE ==> NZE ==> NZE as NZtimes_wd.
Proof.
congruence.
Qed.

Theorem NZinduction :
  forall A : nat -> Prop, predicate_wd (@eq nat) A ->
    A 0 -> (forall n : nat, A n <-> A (S n)) -> forall n : nat, A n.
Proof.
intros A A_wd A0 AS. apply nat_ind. assumption. intros; now apply -> AS.
Qed.

Theorem NZpred_succ : forall n : nat, pred (S n) = n.
Proof.
reflexivity.
Qed.

Theorem NZplus_0_l : forall n : nat, 0 + n = n.
Proof.
reflexivity.
Qed.

Theorem NZplus_succ_l : forall n m : nat, (S n) + m = S (n + m).
Proof.
reflexivity.
Qed.

Theorem NZminus_0_r : forall n : nat, n - 0 = n.
Proof.
intro n; now destruct n.
Qed.

Theorem NZminus_succ_r : forall n m : nat, n - (S m) = pred (n - m).
Proof.
intros n m; induction n m using nat_double_ind; simpl; auto. apply NZminus_0_r.
Qed.

Theorem NZtimes_0_r : forall n : nat, n * 0 = 0.
Proof.
exact mult_0_r.
Qed.

Theorem NZtimes_succ_r : forall n m : nat, n * (S m) = n * m + n.
Proof.
intros n m; symmetry; apply mult_n_Sm.
Qed.

End NZAxiomsMod.

Definition NZlt := lt.
Definition NZle := le.

Add Morphism NZlt with signature NZE ==> NZE ==> iff as NZlt_wd.
Proof.
unfold NZE; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Add Morphism NZle with signature NZE ==> NZE ==> iff as NZle_wd.
Proof.
unfold NZE; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Theorem NZle_lt_or_eq : forall n m : nat, n <= m <-> n < m \/ n = m.
Proof.
intros n m; split.
apply le_lt_or_eq.
intro H; destruct H as [H | H].
now apply lt_le_weak. rewrite H; apply le_refl.
Qed.

Theorem NZlt_irrefl : forall n : nat, ~ (n < n).
Proof.
exact lt_irrefl.
Qed.

Theorem NZlt_succ_le : forall n m : nat, n < S m <-> n <= m.
Proof.
intros n m; split; [apply lt_n_Sm_le | apply le_lt_n_Sm].
Qed.

End NZOrdAxiomsMod.

Definition recursion : forall A : Set, A -> (nat -> A -> A) -> nat -> A :=
  fun A : Set => nat_rec (fun _ => A).
Implicit Arguments recursion [A].

Theorem succ_neq_0 : forall n : nat, S n <> 0.
Proof.
intros; discriminate.
Qed.

Theorem pred_0 : pred 0 = 0.
Proof.
reflexivity.
Qed.

Theorem recursion_wd : forall (A : Set) (EA : relation A),
  forall a a' : A, EA a a' ->
    forall f f' : nat -> A -> A, eq_fun2 (@eq nat) EA EA f f' ->
      forall n n' : nat, n = n' ->
        EA (recursion a f n) (recursion a' f' n').
Proof.
unfold eq_fun2; induction n; intros n' Enn'; rewrite <- Enn' in *; simpl; auto.
Qed.

Theorem recursion_0 :
  forall (A : Set) (a : A) (f : nat -> A -> A), recursion a f 0 = a.
Proof.
reflexivity.
Qed.

Theorem recursion_succ :
  forall (A : Set) (EA : relation A) (a : A) (f : nat -> A -> A),
    EA a a -> fun2_wd (@eq nat) EA EA f ->
      forall n : nat, EA (recursion a f (S n)) (f n (recursion a f n)).
Proof.
unfold eq_fun2; induction n; simpl; auto.
Qed.

End NPeanoAxiomsMod.

(* Now we apply the largest property functor *)

Module Export NPeanoMinusPropMod := NMinusPropFunct NPeanoAxiomsMod.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
