(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Well-founded relations and natural numbers *)

Require Import PeanoNat Lt.

Local Open Scope nat_scope.

Implicit Types m n p : nat.

Section Well_founded_Nat.

Variable A : Type.

Variable f : A -> nat.
Definition ltof (a b:A) := f a < f b.
Definition gtof (a b:A) := f b > f a.

Theorem well_founded_ltof : well_founded ltof.
Proof.
  assert (H : forall n (a:A), f a < n -> Acc ltof a).
  { induction n.
    - intros; absurd (f a < 0); auto with arith.
    - intros a Ha. apply Acc_intro. unfold ltof at 1. intros b Hb.
      apply IHn. apply Nat.lt_le_trans with (f a); auto with arith. }
  intros a. apply (H (S (f a))). auto with arith.
Defined.

Theorem well_founded_gtof : well_founded gtof.
Proof.
  exact well_founded_ltof.
Defined.

(** It is possible to directly prove the induction principle going
   back to primitive recursion on natural numbers ([induction_ltof1])
   or to use the previous lemmas to extract a program with a fixpoint
   ([induction_ltof2])

the ML-like program for [induction_ltof1] is :
[[
let induction_ltof1 f F a =
  let rec indrec n k =
    match n with
    | O -> error
    | S m -> F k (indrec m)
  in indrec (f a + 1) a
]]

the ML-like program for [induction_ltof2] is :
[[
   let induction_ltof2 F a = indrec a
   where rec indrec a = F a indrec;;
]]
*)

Theorem induction_ltof1 :
  forall P:A -> Set,
    (forall x:A, (forall y:A, ltof y x -> P y) -> P x) -> forall a:A, P a.
Proof.
  intros P F.
  assert (H : forall n (a:A), f a < n -> P a).
  { induction n.
    - intros; absurd (f a < 0); auto with arith.
    - intros a Ha. apply F. unfold ltof. intros b Hb.
      apply IHn. apply Nat.lt_le_trans with (f a); auto with arith. }
  intros a. apply (H (S (f a))). auto with arith.
Defined.

Theorem induction_gtof1 :
  forall P:A -> Set,
    (forall x:A, (forall y:A, gtof y x -> P y) -> P x) -> forall a:A, P a.
Proof.
  exact induction_ltof1.
Defined.

Theorem induction_ltof2 :
  forall P:A -> Set,
    (forall x:A, (forall y:A, ltof y x -> P y) -> P x) -> forall a:A, P a.
Proof.
  exact (well_founded_induction well_founded_ltof).
Defined.

Theorem induction_gtof2 :
  forall P:A -> Set,
    (forall x:A, (forall y:A, gtof y x -> P y) -> P x) -> forall a:A, P a.
Proof.
  exact induction_ltof2.
Defined.

(** If a relation [R] is compatible with [lt] i.e. if [x R y => f(x) < f(y)]
    then [R] is well-founded. *)

Variable R : A -> A -> Prop.

Hypothesis H_compat : forall x y:A, R x y -> f x < f y.

Theorem well_founded_lt_compat : well_founded R.
Proof.
  assert (H : forall n (a:A), f a < n -> Acc R a).
  { induction n.
    - intros; absurd (f a < 0); auto with arith.
    - intros a Ha. apply Acc_intro. intros b Hb.
      apply IHn. apply Nat.lt_le_trans with (f a); auto with arith. }
  intros a. apply (H (S (f a))). auto with arith.
Defined.

End Well_founded_Nat.

Lemma lt_wf : well_founded lt.
Proof.
  exact (well_founded_ltof nat (fun m => m)).
Defined.

Lemma lt_wf_rec1 :
  forall n (P:nat -> Set), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof.
  exact (fun p P F => induction_ltof1 nat (fun m => m) P F p).
Defined.

Lemma lt_wf_rec :
  forall n (P:nat -> Set), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof.
  exact (fun p P F => induction_ltof2 nat (fun m => m) P F p).
Defined.

Lemma lt_wf_ind :
  forall n (P:nat -> Prop), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof.
  intro p; intros; elim (lt_wf p); auto with arith.
Qed.

Lemma gt_wf_rec :
  forall n (P:nat -> Set), (forall n, (forall m, n > m -> P m) -> P n) -> P n.
Proof.
  exact lt_wf_rec.
Defined.

Lemma gt_wf_ind :
  forall n (P:nat -> Prop), (forall n, (forall m, n > m -> P m) -> P n) -> P n.
Proof lt_wf_ind.

Lemma lt_wf_double_rec :
 forall P:nat -> nat -> Set,
   (forall n m,
     (forall p q, p < n -> P p q) ->
     (forall p, p < m -> P n p) -> P n m) -> forall n m, P n m.
Proof.
  intros P Hrec p; pattern p; apply lt_wf_rec.
  intros n H q; pattern q; apply lt_wf_rec; auto with arith.
Defined.

Lemma lt_wf_double_ind :
  forall P:nat -> nat -> Prop,
    (forall n m,
      (forall p (q:nat), p < n -> P p q) ->
      (forall p, p < m -> P n p) -> P n m) -> forall n m, P n m.
Proof.
  intros P Hrec p; pattern p; apply lt_wf_ind.
  intros n H q; pattern q; apply lt_wf_ind; auto with arith.
Qed.

Hint Resolve lt_wf: arith.
Hint Resolve well_founded_lt_compat: arith.

Section LT_WF_REL.
  Variable A : Set.
  Variable R : A -> A -> Prop.

  (* Relational form of inversion *)
  Variable F : A -> nat -> Prop.
  Definition inv_lt_rel x y := exists2 n, F x n & (forall m, F y m -> n < m).

  Hypothesis F_compat : forall x y:A, R x y -> inv_lt_rel x y.
  Remark acc_lt_rel : forall x:A, (exists n, F x n) -> Acc R x.
  Proof.
    intros x [n fxn]; generalize dependent x.
    pattern n; apply lt_wf_ind; intros.
    constructor; intros.
    destruct (F_compat y x) as (x0,H1,H2); trivial.
    apply (H x0); auto.
  Qed.

  Theorem well_founded_inv_lt_rel_compat : well_founded R.
  Proof.
    constructor; intros.
    case (F_compat y a); trivial; intros.
    apply acc_lt_rel; trivial.
    exists x; trivial.
  Qed.

End LT_WF_REL.

Lemma well_founded_inv_rel_inv_lt_rel :
  forall (A:Set) (F:A -> nat -> Prop), well_founded (inv_lt_rel A F).
Proof.
  intros; apply (well_founded_inv_lt_rel_compat A (inv_lt_rel A F) F); trivial.
Qed.

(** A constructive proof that any non empty decidable subset of
    natural numbers has a least element *)

Set Implicit Arguments.

Require Import Le.
Require Import Compare_dec.
Require Import Decidable.

Definition has_unique_least_element (A:Type) (R:A->A->Prop) (P:A->Prop) :=
  exists! x, P x /\ forall x', P x' -> R x x'.

Lemma dec_inh_nat_subset_has_unique_least_element :
  forall P:nat->Prop, (forall n, P n \/ ~ P n) ->
    (exists n, P n) -> has_unique_least_element le P.
Proof.
  intros P Pdec (n0,HPn0).
  assert
    (forall n, (exists n', n'<n /\ P n' /\ forall n'', P n'' -> n'<=n'')
               \/ (forall n', P n' -> n<=n')).
  { induction n.
    - right. intros. apply Nat.le_0_l.
    - destruct IHn as [(n' & IH1 & IH2)|IH].
      + left. exists n'; auto with arith.
      + destruct (Pdec n) as [HP|HP].
        * left. exists n; auto with arith.
        * right. intros n' Hn'.
          apply Nat.le_neq; split; auto. intros <-. auto. }
  destruct (H n0) as [(n & H1 & H2 & H3)|H0]; [exists n | exists n0];
   repeat split; trivial;
   intros n' (HPn',Hn'); apply Nat.le_antisymm; auto.
Qed.

Unset Implicit Arguments.

Notation iter_nat n A f x := (nat_rect (fun _ => A) x (fun _ => f) n) (only parsing).
