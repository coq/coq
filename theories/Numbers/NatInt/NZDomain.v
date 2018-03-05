(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export NumPrelude NZAxioms.
Require Import NZBase NZOrder NZAddOrder Plus Minus.

(** In this file, we investigate the shape of domains satisfying
    the [NZDomainSig] interface. In particular, we define a
    translation from Peano numbers [nat] into NZ.
*)

Local Notation "f ^ n" := (fun x => nat_rect _ x (fun _ => f) n).

Instance nat_rect_wd n {A} (R:relation A) :
 Proper (R==>(R==>R)==>R) (fun x f => nat_rect (fun _ => _) x (fun _ => f) n).
Proof.
intros x y eq_xy f g eq_fg; induction n; [assumption | now apply eq_fg].
Qed.

Module NZDomainProp (Import NZ:NZDomainSig').
Include NZBaseProp NZ.

(** * Relationship between points thanks to [succ] and [pred]. *)

(** For any two points, one is an iterated successor of the other. *)

Lemma itersucc_or_itersucc n m : exists k, n == (S^k) m \/ m == (S^k) n.
Proof.
revert n.
apply central_induction with (z:=m).
 { intros x y eq_xy; apply ex_iff_morphism.
  intros n; apply or_iff_morphism.
 + split; intros; etransitivity; try eassumption; now symmetry.
 + split; intros; (etransitivity; [eassumption|]); [|symmetry];
    (eapply nat_rect_wd; [eassumption|apply succ_wd]).
 }
exists 0%nat. now left.
intros n. split; intros [k [L|R]].
exists (Datatypes.S k). left. now apply succ_wd.
destruct k as [|k].
simpl in R. exists 1%nat. left. now apply succ_wd.
rewrite nat_rect_succ_r in R. exists k. now right.
destruct k as [|k]; simpl in L.
exists 1%nat. now right.
apply succ_inj in L. exists k. now left.
exists (Datatypes.S k). right. now rewrite nat_rect_succ_r.
Qed.

(** Generalized version of [pred_succ] when iterating *)

Lemma succ_swap_pred : forall k n m, n == (S^k) m -> m == (P^k) n.
Proof.
induction k.
simpl; auto with *.
simpl; intros. apply pred_wd in H. rewrite pred_succ in H. apply IHk in H; auto.
rewrite <- nat_rect_succ_r in H; auto.
Qed.

(** From a given point, all others are iterated successors
    or iterated predecessors. *)

Lemma itersucc_or_iterpred : forall n m, exists k, n == (S^k) m \/ n == (P^k) m.
Proof.
intros n m. destruct (itersucc_or_itersucc n m) as (k,[H|H]).
exists k; left; auto.
exists k; right. apply succ_swap_pred; auto.
Qed.

(** In particular, all points are either iterated successors of [0]
    or iterated predecessors of [0] (or both). *)

Lemma itersucc0_or_iterpred0 :
 forall n, exists p:nat, n == (S^p) 0 \/ n == (P^p) 0.
Proof.
 intros n. exact (itersucc_or_iterpred n 0).
Qed.

(** * Study of initial point w.r.t. [succ] (if any). *)

Definition initial n := forall m, n ~= S m.

Lemma initial_alt : forall n, initial n <-> S (P n) ~= n.
Proof.
split. intros Bn EQ. symmetry in EQ. destruct (Bn _ EQ).
intros NEQ m EQ. apply NEQ. rewrite EQ, pred_succ; auto with *.
Qed.

Lemma initial_alt2 : forall n, initial n <-> ~exists m, n == S m.
Proof. firstorder. Qed.

(** First case: let's assume such an initial point exists
    (i.e. [S] isn't surjective)... *)

Section InitialExists.
Hypothesis init : t.
Hypothesis Initial : initial init.

(** ... then we have unicity of this initial point. *)

Lemma initial_unique : forall m, initial m -> m == init.
Proof.
intros m Im. destruct (itersucc_or_itersucc init m) as (p,[H|H]).
destruct p. now simpl in *. destruct (Initial _ H).
destruct p. now simpl in *. destruct (Im _ H).
Qed.

(** ... then all other points are descendant of it. *)

Lemma initial_ancestor : forall m, exists p, m == (S^p) init.
Proof.
intros m. destruct (itersucc_or_itersucc init m) as (p,[H|H]).
destruct p; simpl in *; auto. exists O; auto with *. destruct (Initial _ H).
exists p; auto.
Qed.

(** NB : We would like to have [pred n == n] for the initial element,
    but nothing forces that. For instance we can have -3 as initial point,
    and P(-3) = 2. A bit odd indeed, but legal according to [NZDomainSig].
    We can hence have [n == (P^k) m] without [exists k', m == (S^k') n].
*)

(** We need decidability of [eq] (or classical reasoning) for this: *)

Section SuccPred.
Hypothesis eq_decidable : forall n m, n==m \/ n~=m.
Lemma succ_pred_approx : forall n, ~initial n -> S (P n) == n.
Proof.
intros n NB. rewrite initial_alt in NB.
destruct (eq_decidable (S (P n)) n); auto.
elim NB; auto.
Qed.
End SuccPred.
End InitialExists.

(** Second case : let's suppose now [S] surjective, i.e. no initial point. *)

Section InitialDontExists.

Hypothesis succ_onto : forall n, exists m, n == S m.

Lemma succ_onto_gives_succ_pred : forall n, S (P n) == n.
Proof.
intros n. destruct (succ_onto n) as (m,H). rewrite H, pred_succ; auto with *.
Qed.

Lemma succ_onto_pred_injective : forall n m, P n == P m -> n == m.
Proof.
intros n m. intros H; apply succ_wd in H.
rewrite !succ_onto_gives_succ_pred in H; auto.
Qed.

End InitialDontExists.


(** To summarize:

  S is always injective, P is always surjective  (thanks to [pred_succ]).

  I) If S is not surjective, we have an initial point, which is unique.
     This bottom is below zero: we have N shifted (or not) to the left.
     P cannot be injective: P init = P (S (P init)).
     (P init) can be arbitrary.

  II) If S is surjective, we have [forall n, S (P n) = n], S and P are
     bijective and reciprocal.

     IIa) if [exists k<>O, 0 == S^k 0], then we have a cyclic structure Z/nZ
     IIb) otherwise, we have Z
*)


(** * An alternative induction principle using [S] and [P]. *)

(** It is weaker than [bi_induction]. For instance it cannot prove that
    we can go from one point by many [S] _or_ many [P], but only by many
    [S] mixed with many [P]. Think of a model with two copies of N:

    0,  1=S 0,   2=S 1, ...
    0', 1'=S 0', 2'=S 1', ...

    and P 0 = 0' and P 0' = 0.
*)

Lemma bi_induction_pred :
  forall A : t -> Prop, Proper (eq==>iff) A ->
    A 0 -> (forall n, A n -> A (S n)) -> (forall n, A n -> A (P n)) ->
    forall n, A n.
Proof.
intros. apply bi_induction; auto.
clear n. intros n; split; auto.
intros G; apply H2 in G. rewrite pred_succ in G; auto.
Qed.

Lemma central_induction_pred :
  forall A : t -> Prop, Proper (eq==>iff) A -> forall n0,
    A n0 -> (forall n, A n -> A (S n)) -> (forall n, A n -> A (P n)) ->
    forall n, A n.
Proof.
intros.
assert (A 0).
destruct (itersucc_or_iterpred 0 n0) as (k,[Hk|Hk]); rewrite Hk; clear Hk.
 clear H2. induction k; simpl in *; auto.
 clear H1. induction k; simpl in *; auto.
apply bi_induction_pred; auto.
Qed.

End NZDomainProp.

(** We now focus on the translation from [nat] into [NZ].
    First, relationship with [0], [succ], [pred].
*)

Module NZOfNat (Import NZ:NZDomainSig').

Definition ofnat (n : nat) : t := (S^n) 0.
Notation "[ n ]" := (ofnat n) (at level 7) : ofnat.
Local Open Scope ofnat.

Lemma ofnat_zero : [O] == 0.
Proof.
reflexivity.
Qed.

Lemma ofnat_succ : forall n, [Datatypes.S n] == succ [n].
Proof.
 now unfold ofnat.
Qed.

Lemma ofnat_pred : forall n, n<>O -> [Peano.pred n] == P [n].
Proof.
 unfold ofnat. destruct n. destruct 1; auto.
 intros _. simpl. symmetry. apply pred_succ.
Qed.

(** Since [P 0] can be anything in NZ (either [-1], [0], or even other
    numbers, we cannot state previous lemma for [n=O]. *)

End NZOfNat.


(** If we require in addition a strict order on NZ, we can prove that
    [ofnat] is injective, and hence that NZ is infinite
    (i.e. we ban Z/nZ models) *)

Module NZOfNatOrd (Import NZ:NZOrdSig').
Include NZOfNat NZ.
Include NZBaseProp NZ <+ NZOrderProp NZ.
Local Open Scope ofnat.

Theorem ofnat_S_gt_0 :
  forall n : nat, 0 < [Datatypes.S n].
Proof.
unfold ofnat.
intros n; induction n as [| n IH]; simpl in *.
apply lt_succ_diag_r.
apply lt_trans with (S 0). apply lt_succ_diag_r. now rewrite <- succ_lt_mono.
Qed.

Theorem ofnat_S_neq_0 :
  forall n : nat, 0 ~= [Datatypes.S n].
Proof.
intros. apply lt_neq, ofnat_S_gt_0.
Qed.

Lemma ofnat_injective : forall n m, [n]==[m] -> n = m.
Proof.
induction n as [|n IH]; destruct m; auto.
intros H; elim (ofnat_S_neq_0 _ H).
intros H; symmetry in H; elim (ofnat_S_neq_0 _ H).
intros. f_equal. apply IH. now rewrite <- succ_inj_wd.
Qed.

Lemma ofnat_eq : forall n m, [n]==[m] <-> n = m.
Proof.
split. apply ofnat_injective. intros; now subst.
Qed.

(* In addition, we can prove that [ofnat] preserves order. *)

Lemma ofnat_lt : forall n m : nat, [n]<[m] <-> (n<m)%nat.
Proof.
induction n as [|n IH]; destruct m; repeat rewrite ofnat_zero; split.
intro H; elim (lt_irrefl _ H).
inversion 1.
auto with arith.
intros; apply ofnat_S_gt_0.
intro H; elim (lt_asymm _ _ H); apply ofnat_S_gt_0.
inversion 1.
rewrite !ofnat_succ, <- succ_lt_mono, IH; auto with arith.
rewrite !ofnat_succ, <- succ_lt_mono, IH; auto with arith.
Qed.

Lemma ofnat_le : forall n m : nat, [n]<=[m] <-> (n<=m)%nat.
Proof.
intros. rewrite lt_eq_cases, ofnat_lt, ofnat_eq.
split.
destruct 1; subst; auto with arith.
apply Lt.le_lt_or_eq.
Qed.

End NZOfNatOrd.


(** For basic operations, we can prove correspondance with
    their counterpart in [nat]. *)

Module NZOfNatOps (Import NZ:NZAxiomsSig').
Include NZOfNat NZ.
Local Open Scope ofnat.

Lemma ofnat_add_l : forall n m, [n]+m == (S^n) m.
Proof.
 induction n; intros.
 apply add_0_l.
 rewrite ofnat_succ, add_succ_l. simpl. now f_equiv.
Qed.

Lemma ofnat_add : forall n m, [n+m] == [n]+[m].
Proof.
 intros. rewrite ofnat_add_l.
 induction n; simpl. reflexivity.
 now f_equiv.
Qed.

Lemma ofnat_mul : forall n m, [n*m] == [n]*[m].
Proof.
 induction n; simpl; intros.
 symmetry. apply mul_0_l.
 rewrite plus_comm.
 rewrite ofnat_add, mul_succ_l.
 now f_equiv.
Qed.

Lemma ofnat_sub_r : forall n m, n-[m] == (P^m) n.
Proof.
 induction m; simpl; intros.
 apply sub_0_r.
 rewrite sub_succ_r. now f_equiv.
Qed.

Lemma ofnat_sub : forall n m, m<=n -> [n-m] == [n]-[m].
Proof.
 intros n m H. rewrite ofnat_sub_r.
 revert n H. induction m. intros.
 rewrite <- minus_n_O. now simpl.
 intros.
 destruct n.
 inversion H.
 rewrite nat_rect_succ_r.
 simpl.
 etransitivity. apply IHm. auto with arith.
    eapply nat_rect_wd; [symmetry;apply pred_succ|apply pred_wd].
Qed.

End NZOfNatOps.
