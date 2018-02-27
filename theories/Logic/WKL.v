(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** A constructive proof of a version of Weak König's Lemma over a
    decidable predicate in the formulation of which infinite paths are
    treated as predicates. The representation of paths as relations
    avoid the need for classical logic and unique choice. The
    decidability condition is sufficient to ensure that some required
    instance of double negation for disjunction of finite paths holds.

    The idea of the proof comes from the proof of the weak König's
    lemma from separation in second-order arithmetic.

    Notice that we do not start from a tree but just from an arbitrary
    predicate. Original Weak Konig's Lemma is the instantiation of
    the lemma to a tree *)

Require Import WeakFan List.
Import ListNotations.

Require Import Omega.

(** [is_path_from P n l] means that there exists a path of length [n]
    from [l] on which [P] does not hold *)

Inductive is_path_from (P:list bool -> Prop) : nat -> list bool -> Prop :=
| here l : ~ P l -> is_path_from P 0 l
| next_left l n : ~ P l -> is_path_from P n (true::l) -> is_path_from P (S n) l
| next_right l n : ~ P l -> is_path_from P n (false::l) -> is_path_from P (S n) l.

(** We give the characterization of is_path_from in terms of a more common arithmetical formula *)

Proposition is_path_from_characterization P n l :
  is_path_from P n l <-> exists l', length l' = n /\ forall n', n'<=n -> ~ P (rev (firstn n' l') ++ l).
Proof.
intros. split.
- induction 1 as [|* HP _ (l'&Hl'&HPl')|* HP _ (l'&Hl'&HPl')].
  + exists []. split. reflexivity. intros n <-%le_n_0_eq. assumption.
  + exists (true :: l'). split. apply eq_S, Hl'. intros [|] H.
    * assumption.
    * simpl. rewrite <- app_assoc. apply HPl', le_S_n, H.
  + exists (false :: l'). split. apply eq_S, Hl'. intros [|] H.
    * assumption.
    * simpl. rewrite <- app_assoc. apply HPl', le_S_n, H.
- intros (l'& <- &HPl'). induction l' as [|[|]] in l, HPl' |- *.
  + constructor. apply (HPl' 0). apply le_0_n.
  + eapply next_left.
    * apply (HPl' 0), le_0_n.
    * fold (length l'). apply IHl'. intros n' H%le_n_S. apply HPl' in H. simpl in H. rewrite <- app_assoc in H. assumption.
  + apply next_right.
    * apply (HPl' 0), le_0_n.
    * fold (length l'). apply IHl'. intros n' H%le_n_S. apply HPl' in H. simpl in H. rewrite <- app_assoc in H. assumption.
Qed.

(** [infinite_from P l] means that we can find arbitrary long paths
    along which [P] does not hold above [l] *)

Definition infinite_from (P:list bool -> Prop) l := forall n, is_path_from P n l.

(** [has_infinite_path P] means that there is an infinite path
    (represented as a predicate) along which [P] does not hold at all *)

Definition has_infinite_path (P:list bool -> Prop) :=
  exists (X:nat -> Prop), forall l, approx X l -> ~ P l.

(** [inductively_barred_at P n l] means that [P] eventually holds above
    [l] after at most [n] steps upwards *)

Inductive inductively_barred_at (P:list bool -> Prop) : nat -> list bool -> Prop :=
| now_at l n : P l -> inductively_barred_at P n l
| propagate_at l n :
    inductively_barred_at P n (true::l) ->
    inductively_barred_at P n (false::l) ->
    inductively_barred_at P (S n) l.

(** The proof proceeds by building a set [Y] of finite paths
   approximating either the smallest unbarred infinite path in [P], if
   there is one (taking [true]>[false]), or the path
   true::true::... if [P] happens to be inductively_barred *)

Fixpoint Y P (l:list bool) :=
  match l with
  | [] => True
  | b::l =>
      Y P l /\
      if b then exists n, inductively_barred_at P n (false::l) else infinite_from P (false::l)
  end.

Require Import Compare_dec Le Lt.

Lemma is_path_from_restrict : forall P n n' l, n <= n' ->
  is_path_from P n' l -> is_path_from P n l.
Proof.
intros * Hle H; induction H in n, Hle, H |- * ; intros.
- apply le_n_0_eq in Hle as <-. apply here. assumption.
- destruct n.
  + apply here. assumption.
  + apply next_left; auto using le_S_n.
- destruct n.
  + apply here. assumption.
  + apply next_right; auto using le_S_n.
Qed.

Lemma inductively_barred_at_monotone : forall P l n n', n' <= n ->
  inductively_barred_at P n' l -> inductively_barred_at P n l.
Proof.
intros * Hle Hbar.
induction Hbar in n, l, Hle, Hbar |- *.
- apply now_at; auto.
- destruct n; [apply le_Sn_0 in Hle; contradiction|].
  apply le_S_n in Hle.
  apply propagate_at; auto.
Qed.

Definition demorgan_or (P:list bool -> Prop) l l' := ~ (P l /\ P l') -> ~ P l \/ ~ P l'.

Definition demorgan_inductively_barred_at P :=
  forall n l, demorgan_or (inductively_barred_at P n) (true::l) (false::l).

Lemma inductively_barred_at_imp_is_path_from :
  forall P, demorgan_inductively_barred_at P -> forall n l,
  ~ inductively_barred_at P n l -> is_path_from P n l.
Proof.
intros P Hdemorgan; induction n; intros l H.
- apply here.
  intro. apply H.
  apply now_at. auto.
- assert (H0:~ (inductively_barred_at P n (true::l) /\ inductively_barred_at P n (false::l)))
  by firstorder using inductively_barred_at.
  assert (HnP:~ P l) by firstorder using inductively_barred_at.
  apply Hdemorgan in H0 as [H0|H0]; apply IHn in H0; auto using is_path_from.
Qed.

Lemma is_path_from_imp_inductively_barred_at : forall P n l,
   is_path_from P n l -> inductively_barred_at P n l -> False.
Proof.
intros P; induction n; intros l H1 H2.
- inversion_clear H1. inversion_clear H2. auto.
- inversion_clear H1.
  + inversion_clear H2.
    * auto.
    * apply IHn with (true::l); auto.
  + inversion_clear H2.
    * auto.
    * apply IHn with (false::l); auto.
Qed.

Lemma find_left_path : forall P l n,
  is_path_from P (S n) l -> inductively_barred_at P n (false :: l) -> is_path_from P n (true :: l).
Proof.
inversion 1; subst; intros.
- auto.
- exfalso. eauto using is_path_from_imp_inductively_barred_at.
Qed.

Lemma Y_unique : forall P, demorgan_inductively_barred_at P ->
  forall l1 l2, length l1 = length l2 -> Y P l1 -> Y P l2 -> l1 = l2.
Proof.
intros * DeMorgan. induction l1, l2.
- trivial.
- discriminate.
- discriminate.
- intros [= H] (HY1,H1) (HY2,H2).
  pose proof (IHl1 l2 H HY1 HY2). clear HY1 HY2 H IHl1.
  subst l1.
  f_equal.
  destruct a, b; try reflexivity.
  + destruct H1 as (n,Hbar).
    destruct (is_path_from_imp_inductively_barred_at _ _ _ (H2 n) Hbar).
  + destruct H2 as (n,Hbar).
    destruct (is_path_from_imp_inductively_barred_at _ _ _ (H1 n) Hbar).
Qed.

(** [X] is the translation of [Y] as a predicate *)

Definition X P n := exists l, length l = n /\ Y P (true::l).

Lemma Y_approx : forall P, demorgan_inductively_barred_at P ->
  forall l, approx (X P) l -> Y P l.
Proof.
intros P DeMorgan. induction l.
- trivial.
- intros (H,Hb). split.
  + auto.
  + unfold X in Hb.
    destruct a.
    * destruct Hb as (l',(Hl',(HYl',HY))).
      rewrite <- (Y_unique P DeMorgan l' l Hl'); auto.
    * intro n. apply inductively_barred_at_imp_is_path_from. assumption.
      firstorder.
Qed.

(** Main theorem *)

Theorem PreWeakKonigsLemma : forall P,
  demorgan_inductively_barred_at P -> infinite_from P [] -> has_infinite_path P.
Proof.
intros P DeMorgan Hinf.
exists (X P). intros l Hl.
assert (infinite_from P l).
{ induction l.
  - assumption.
  - destruct Hl as (Hl,Ha).
    intros n.
    pose proof (IHl Hl) as IHl'. clear IHl.
    apply Y_approx in Hl; [|assumption].
    destruct a.
    + destruct Ha as (l'&Hl'&HY'&n'&Hbar).
      rewrite (Y_unique _ DeMorgan _ _ Hl' HY' Hl) in Hbar.
      destruct (le_lt_dec n n') as [Hle|Hlt].
      * specialize (IHl' (S n')).
        apply is_path_from_restrict with n'; [assumption|].
        apply find_left_path; trivial.
      * specialize (IHl' (S n)).
        apply inductively_barred_at_monotone with (n:=n) in Hbar; [|apply lt_le_weak, Hlt].
        apply find_left_path; trivial.
    + apply inductively_barred_at_imp_is_path_from; firstorder. }
specialize (H 0). inversion H. assumption.
Qed.

Lemma inductively_barred_at_decidable :
  forall P, (forall l, P l \/ ~ P l) -> forall n l, inductively_barred_at P n l \/ ~ inductively_barred_at P n l.
Proof.
intros P HP. induction n; intros.
- destruct (HP l).
  + left. apply now_at, H.
  + right. inversion 1. auto.
- destruct (HP l).
  + left. apply now_at, H.
  + destruct (IHn (true::l)).
    * destruct (IHn (false::l)).
      { left. apply propagate_at; assumption. }
      { right. inversion_clear 1; auto. }
    * right. inversion_clear 1; auto.
Qed.

Lemma inductively_barred_at_is_path_from_decidable :
  forall P, (forall l, P l \/ ~ P l) -> demorgan_inductively_barred_at P.
Proof.
intros P Hdec n l H.
destruct (inductively_barred_at_decidable P Hdec n (true::l)).
- destruct (inductively_barred_at_decidable P Hdec n (false::l)).
  + auto.
  + auto.
- auto.
Qed.

(** Main corollary *)

Corollary WeakKonigsLemma : forall P, (forall l, P l \/ ~ P l) ->
  infinite_from P [] -> has_infinite_path P.
Proof.
intros P Hdec Hinf.
apply inductively_barred_at_is_path_from_decidable in Hdec.
apply PreWeakKonigsLemma; assumption.
Qed.
