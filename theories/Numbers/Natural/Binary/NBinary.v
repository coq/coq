Require Import NArith.
Require Import NMinus.

Module NBinaryAxiomsMod <: NAxiomsSig.
Open Local Scope N_scope.
Module Export NZOrdAxiomsMod <: NZOrdAxiomsSig.
Module Export NZAxiomsMod <: NZAxiomsSig.

Definition NZ := N.
Definition NZeq := (@eq N).
Definition NZ0 := 0.
Definition NZsucc := Nsucc.
Definition NZpred := Npred.
Definition NZplus := Nplus.
Definition NZminus := Nminus.
Definition NZtimes := Nmult.

Theorem NZE_equiv : equiv N NZeq.
Proof (eq_equiv N).

Add Relation N NZeq
 reflexivity proved by (proj1 NZE_equiv)
 symmetry proved by (proj2 (proj2 NZE_equiv))
 transitivity proved by (proj1 (proj2 NZE_equiv))
as NZE_rel.

Add Morphism NZsucc with signature NZeq ==> NZeq as NZsucc_wd.
Proof.
congruence.
Qed.

Add Morphism NZpred with signature NZeq ==> NZeq as NZpred_wd.
Proof.
congruence.
Qed.

Add Morphism NZplus with signature NZeq ==> NZeq ==> NZeq as NZplus_wd.
Proof.
congruence.
Qed.

Add Morphism NZminus with signature NZeq ==> NZeq ==> NZeq as NZminus_wd.
Proof.
congruence.
Qed.

Add Morphism NZtimes with signature NZeq ==> NZeq ==> NZeq as NZtimes_wd.
Proof.
congruence.
Qed.

Theorem NZinduction :
  forall A : N -> Prop, predicate_wd NZeq A ->
    A 0 -> (forall n, A n <-> A (Nsucc n)) -> forall n : N, A n.
Proof.
intros A A_wd A0 AS. apply Nind. assumption. intros; now apply -> AS.
Qed.

Theorem NZpred_succ : forall n : N, Npred (Nsucc n) = n.
Proof.
destruct n as [| p]; simpl. reflexivity.
case_eq (Psucc p); try (intros q H; rewrite <- H; now rewrite Ppred_succ).
intro H; false_hyp H Psucc_not_one.
Qed.

Theorem NZplus_0_l : forall n : N, 0 + n = n.
Proof Nplus_0_l.

Theorem NZplus_succ_l : forall n m : N, (Nsucc n) + m = Nsucc (n + m).
Proof Nplus_succ.

Theorem NZminus_0_r : forall n : N, n - 0 = n.
Proof Nminus_0_r.

Theorem NZminus_succ_r : forall n m : N, n - (Nsucc m) = Npred (n - m).
Proof Nminus_succ_r.

Theorem NZtimes_0_r : forall n : N, n * 0 = 0.
Proof.
intro n; rewrite Nmult_comm; apply Nmult_0_l.
Qed.

Theorem NZtimes_succ_r : forall n m : N, n * (Nsucc m) = n * m + n.
Proof.
intros n m; rewrite Nmult_comm, Nmult_Sn_m.
now rewrite Nplus_comm, Nmult_comm.
Qed.

End NZAxiomsMod.

Definition NZlt := Nlt.
Definition NZle := Nle.

Add Morphism NZlt with signature NZeq ==> NZeq ==> iff as NZlt_wd.
Proof.
unfold NZeq; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Add Morphism NZle with signature NZeq ==> NZeq ==> iff as NZle_wd.
Proof.
unfold NZeq; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Theorem NZle_lt_or_eq : forall n m : N, n <= m <-> n < m \/ n = m.
Proof.
intros n m.
assert (H : (n ?= m) = Eq <-> n = m).
split; intro H; [now apply Ncompare_Eq_eq | rewrite H; apply Ncompare_refl].
unfold Nle, Nlt. rewrite <- H.
destruct (n ?= m); split; intro H1; (try discriminate); try (now left); try now right.
now elim H1. destruct H1; discriminate.
Qed.

Theorem NZlt_irrefl : forall n : N, ~ n < n.
Proof Nlt_irrefl.

Theorem NZlt_succ_le : forall n m : N, n < (Nsucc m) <-> n <= m.
Proof.
intros x y. rewrite NZle_lt_or_eq.
unfold Nlt, Nle; apply Ncompare_n_Sm.
Qed.

End NZOrdAxiomsMod.

Definition recursion (A : Set) (a : A) (f : N -> A -> A) (n : N) :=
  Nrec (fun _ => A) a f n.
Implicit Arguments recursion [A].

Theorem succ_neq_0 : forall n : N, Nsucc n <> 0.
Proof Nsucc_0.

Theorem pred_0 : Npred 0 = 0.
Proof.
reflexivity.
Qed.

Theorem recursion_wd :
forall (A : Set) (Aeq : relation A),
  forall a a' : A, Aeq a a' ->
    forall f f' : N -> A -> A, eq_fun2 NZeq Aeq Aeq f f' ->
      forall x x' : N, x = x' ->
        Aeq (recursion a f x) (recursion a' f' x').
Proof.
unfold fun2_wd, NZeq, eq_fun2.
intros A Aeq a a' Eaa' f f' Eff'.
intro x; pattern x; apply Nind.
intros x' H; now rewrite <- H.
clear x.
intros x IH x' H; rewrite <- H.
unfold recursion, Nrec in *; do 2 rewrite Nrect_step.
now apply Eff'; [| apply IH].
Qed.

Theorem recursion_0 :
  forall (A : Set) (a : A) (f : N -> A -> A), recursion a f 0 = a.
Proof.
intros A a f; unfold recursion; unfold Nrec; now rewrite Nrect_base.
Qed.

Theorem recursion_succ :
  forall (A : Set) (Aeq : relation A) (a : A) (f : N -> A -> A),
    Aeq a a -> fun2_wd NZeq Aeq Aeq f ->
      forall n : N, Aeq (recursion a f (Nsucc n)) (f n (recursion a f n)).
Proof.
unfold NZeq, recursion, Nrec, fun2_wd; intros A Aeq a f EAaa f_wd n; pattern n; apply Nind.
rewrite Nrect_step; rewrite Nrect_base; now apply f_wd.
clear n; intro n; do 2 rewrite Nrect_step; intro IH. apply f_wd; [reflexivity|].
now rewrite Nrect_step.
Qed.

End NBinaryAxiomsMod.

Module Export NBinaryMinusPropMod := NMinusPropFunct NBinaryAxiomsMod.

(* Some fun comparing the efficiency of the generic log defined
by strong (course-of-value) recursion and the log defined by recursion
on notation *)
(* Time Eval compute in (log 100000). *) (* 98 sec *)

(*
Fixpoint binposlog (p : positive) : N :=
match p with
| xH => 0
| xO p' => Nsucc (binposlog p')
| xI p' => Nsucc (binposlog p')
end.

Definition binlog (n : N) : N :=
match n with
| 0 => 0
| Npos p => binposlog p
end.
*)
(* Eval compute in (binlog 1000000000000000000). *) (* Works very fast *)

