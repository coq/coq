(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i i*)

Require Import BinPos.
Require Import NMinus.

(** Definitions *)

Inductive N : Set :=
| N0 : N
| Npos : positive -> N.

Definition succ n :=
match n with
| N0 => Npos 1
| Npos p => Npos (Psucc p)
end.

Definition pred (n : N) :=
match n with
| N0 => N0
| Npos p =>
  match p with
  | xH => N0
  | _ => Npos (Ppred p)
  end
end.

Definition plus n m :=
match n, m with
| N0, _ => m
| _, N0 => n
| Npos p, Npos q => Npos (p + q)
end.

Definition minus (n m : N) :=
match n, m with
| N0, _ => N0
| n, N0 => n
| Npos n', Npos m' =>
  match Pminus_mask n' m' with
  | IsPos p => Npos p
  | _ => N0
  end
end.

Definition times n m :=
match n, m with
| N0, _ => N0
| _, N0 => N0
| Npos p, Npos q => Npos (p * q)
end.

Definition Ncompare n m :=
match n, m with
| N0, N0 => Eq
| N0, Npos m' => Lt
| Npos n', N0 => Gt
| Npos n', Npos m' => (n' ?= m')%positive Eq
end.

Definition lt (x y : N) := (Ncompare x y) = Lt.
Definition le (x y : N) := (Ncompare x y) <> Gt.

Definition min (n m : N) :=
match Ncompare n m with
| Lt | Eq => n
| Gt => m
end.

Definition max (n m : N) :=
match Ncompare n m with
| Lt | Eq => m
| Gt => n
end.

Delimit Scope NatScope with Nat.
Bind Scope NatScope with N.

Notation "0" := N0 : NatScope.
Notation "1" := (Npos xH) : NatScope.
Infix "+" := plus : NatScope.
Infix "-" := minus : NatScope.
Infix "*" := times : NatScope.
Infix "?=" := Ncompare (at level 70, no associativity) : NatScope.
Infix "<" := lt : NatScope.
Infix "<=" := le : NatScope.

Open Local Scope NatScope.

(** Peano induction on binary natural numbers *)

Definition Nrect
  (P : N -> Type) (a : P N0)
    (f : forall n : N, P n -> P (succ n)) (n : N) : P n :=
let f' (p : positive) (x : P (Npos p)) := f (Npos p) x in
let P' (p : positive) := P (Npos p) in
match n return (P n) with
| N0 => a
| Npos p => Prect P' (f N0 a) f' p
end.

Theorem Nrect_base : forall P a f, Nrect P a f N0 = a.
Proof.
reflexivity.
Qed.

Theorem Nrect_step : forall P a f n, Nrect P a f (succ n) = f n (Nrect P a f n).
Proof.
intros P a f; destruct n as [| p]; simpl;
[rewrite Prect_base | rewrite Prect_succ]; reflexivity.
Qed.

(*Definition Nind (P : N -> Prop) := Nrect P.

Definition Nrec (P : N -> Set) := Nrect P.

Theorem Nrec_base : forall P a f, Nrec P a f N0 = a.
Proof.
intros P a f; unfold Nrec; apply Nrect_base.
Qed.

Theorem Nrec_step : forall P a f n, Nrec P a f (Nsucc n) = f n (Nrec P a f n).
Proof.
intros P a f; unfold Nrec; apply Nrect_step.
Qed.*)

(** Results about the order *)

Theorem Ncompare_eq_correct : forall n m : N, (n ?= m) = Eq <-> n = m.
Proof.
destruct n as [| n]; destruct m as [| m]; simpl;
split; intro H; try reflexivity; try discriminate H.
apply Pcompare_Eq_eq in H; now rewrite H.
injection H; intro H1; rewrite H1; apply Pcompare_refl.
Qed.

Theorem Ncompare_diag : forall n : N, n ?= n = Eq.
Proof.
intro n; now apply <- Ncompare_eq_correct.
Qed.

Theorem Ncompare_antisymm :
  forall (n m : N) (c : comparison), n ?= m = c -> m ?= n = CompOpp c.
Proof.
destruct n; destruct m; destruct c; simpl; intro H; try discriminate H; try reflexivity;
replace Eq with (CompOpp Eq) by reflexivity; rewrite <- Pcompare_antisym;
now rewrite H.
Qed.

(** Implementation of NAxiomsSig module type *)

Module NBinaryAxiomsMod <: NAxiomsSig.
Module Export NZOrdAxiomsMod <: NZOrdAxiomsSig.
Module Export NZAxiomsMod <: NZAxiomsSig.

Definition NZ := N.
Definition NZeq := (@eq N).
Definition NZ0 := N0.
Definition NZsucc := succ.
Definition NZpred := pred.
Definition NZplus := plus.
Definition NZminus := minus.
Definition NZtimes := times.

Theorem NZeq_equiv : equiv N NZeq.
Proof (eq_equiv N).

Add Relation N NZeq
 reflexivity proved by (proj1 NZeq_equiv)
 symmetry proved by (proj2 (proj2 NZeq_equiv))
 transitivity proved by (proj1 (proj2 NZeq_equiv))
as NZeq_rel.

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
  forall A : NZ -> Prop, predicate_wd NZeq A ->
    A N0 -> (forall n, A n <-> A (NZsucc n)) -> forall n : NZ, A n.
Proof.
intros A A_wd A0 AS. apply Nrect. assumption. intros; now apply -> AS.
Qed.

Theorem NZpred_succ : forall n : NZ, NZpred (NZsucc n) = n.
Proof.
destruct n as [| p]; simpl. reflexivity.
case_eq (Psucc p); try (intros q H; rewrite <- H; now rewrite Ppred_succ).
intro H; false_hyp H Psucc_not_one.
Qed.

Theorem NZplus_0_l : forall n : NZ, N0 + n = n.
Proof.
reflexivity.
Qed.

Theorem NZplus_succ_l : forall n m : NZ, (NZsucc n) + m = NZsucc (n + m).
Proof.
destruct n; destruct m.
simpl in |- *; reflexivity.
unfold NZsucc, NZplus, succ, plus. rewrite <- Pplus_one_succ_l; reflexivity.
simpl in |- *; reflexivity.
simpl in |- *; rewrite Pplus_succ_permute_l; reflexivity.
Qed.

Theorem NZminus_0_r : forall n : NZ, n - N0 = n.
Proof.
now destruct n.
Qed.

Theorem NZminus_succ_r : forall n m : NZ, n - (NZsucc m) = NZpred (n - m).
Proof.
destruct n as [| p]; destruct m as [| q]; try reflexivity.
now destruct p.
simpl. rewrite Pminus_mask_succ_r, Pminus_mask_carry_spec.
now destruct (Pminus_mask p q) as [| r |]; [| destruct r |].
Qed.

Theorem NZtimes_0_r : forall n : NZ, n * N0 = N0.
Proof.
destruct n; reflexivity.
Qed.

Theorem NZtimes_succ_r : forall n m : NZ, n * (NZsucc m) = n * m + n.
Proof.
destruct n as [| n]; destruct m as [| m]; simpl; try reflexivity.
now rewrite Pmult_1_r.
now rewrite (Pmult_comm n (Psucc m)), Pmult_Sn_m, (Pplus_comm n), Pmult_comm.
Qed.

End NZAxiomsMod.

Definition NZlt := lt.
Definition NZle := le.
Definition NZmin := min.
Definition NZmax := max.

Add Morphism NZlt with signature NZeq ==> NZeq ==> iff as NZlt_wd.
Proof.
unfold NZeq; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Add Morphism NZle with signature NZeq ==> NZeq ==> iff as NZle_wd.
Proof.
unfold NZeq; intros x1 x2 H1 y1 y2 H2; rewrite H1; now rewrite H2.
Qed.

Add Morphism NZmin with signature NZeq ==> NZeq ==> NZeq as NZmin_wd.
Proof.
congruence.
Qed.

Add Morphism NZmax with signature NZeq ==> NZeq ==> NZeq as NZmax_wd.
Proof.
congruence.
Qed.

Theorem NZle_lt_or_eq : forall n m : N, n <= m <-> n < m \/ n = m.
Proof.
intros n m. unfold le, lt. rewrite <- Ncompare_eq_correct.
destruct (n ?= m); split; intro H1; (try discriminate); try (now left); try now right.
now elim H1. destruct H1; discriminate.
Qed.

Theorem NZlt_irrefl : forall n : NZ, ~ n < n.
Proof.
intro n; unfold lt; now rewrite Ncompare_diag.
Qed.

Theorem NZlt_succ_le : forall n m : NZ, n < (NZsucc m) <-> n <= m.
Proof.
intros n m; unfold lt, le; destruct n as [| p]; destruct m as [| q]; simpl;
split; intro H; try reflexivity; try discriminate.
destruct p; simpl; intros; discriminate. elimtype False; now apply H.
apply -> Pcompare_p_Sq in H. destruct H as [H | H].
now rewrite H. now rewrite H, Pcompare_refl.
apply <- Pcompare_p_Sq. case_eq ((p ?= q)%positive Eq); intro H1.
right; now apply Pcompare_Eq_eq. now left. elimtype False; now apply H.
Qed.

Theorem NZmin_l : forall n m : N, n <= m -> NZmin n m = n.
Proof.
unfold NZmin, min, le; intros n m H.
destruct (n ?= m); try reflexivity. now elim H.
Qed.

Theorem NZmin_r : forall n m : N, m <= n -> NZmin n m = m.
Proof.
unfold NZmin, min, le; intros n m H.
case_eq (n ?= m); intro H1; try reflexivity.
now apply -> Ncompare_eq_correct.
apply Ncompare_antisymm in H1. now elim H.
Qed.

Theorem NZmax_l : forall n m : N, m <= n -> NZmax n m = n.
Proof.
unfold NZmax, max, le; intros n m H.
case_eq (n ?= m); intro H1; try reflexivity.
symmetry; now apply -> Ncompare_eq_correct.
apply Ncompare_antisymm in H1. now elim H.
Qed.

Theorem NZmax_r : forall n m : N, n <= m -> NZmax n m = m.
Proof.
unfold NZmax, max, le; intros n m H.
destruct (n ?= m); try reflexivity. now elim H.
Qed.

End NZOrdAxiomsMod.

Definition recursion (A : Set) (a : A) (f : N -> A -> A) (n : N) :=
  Nrect (fun _ => A) a f n.
Implicit Arguments recursion [A].

Theorem pred_0 : pred N0 = N0.
Proof.
reflexivity.
Qed.

Theorem recursion_wd :
forall (A : Set) (Aeq : relation A),
  forall a a' : A, Aeq a a' ->
    forall f f' : N -> A -> A, fun2_eq NZeq Aeq Aeq f f' ->
      forall x x' : N, x = x' ->
        Aeq (recursion a f x) (recursion a' f' x').
Proof.
unfold fun2_wd, NZeq, fun2_eq.
intros A Aeq a a' Eaa' f f' Eff'.
intro x; pattern x; apply Nrect.
intros x' H; now rewrite <- H.
clear x.
intros x IH x' H; rewrite <- H.
unfold recursion in *. do 2 rewrite Nrect_step.
now apply Eff'; [| apply IH].
Qed.

Theorem recursion_0 :
  forall (A : Set) (a : A) (f : N -> A -> A), recursion a f N0 = a.
Proof.
intros A a f; unfold recursion; now rewrite Nrect_base.
Qed.

Theorem recursion_succ :
  forall (A : Set) (Aeq : relation A) (a : A) (f : N -> A -> A),
    Aeq a a -> fun2_wd NZeq Aeq Aeq f ->
      forall n : N, Aeq (recursion a f (succ n)) (f n (recursion a f n)).
Proof.
unfold NZeq, recursion, fun2_wd; intros A Aeq a f EAaa f_wd n; pattern n; apply Nrect.
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

