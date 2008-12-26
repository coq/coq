(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** The type [nat] of Peano natural numbers (built from [O] and [S])
    is defined in [Datatypes.v] *)

(** This module defines the following operations on natural numbers :
    - predecessor [pred]
    - addition [plus]
    - multiplication [mult]
    - less or equal order [le]
    - less [lt]
    - greater or equal [ge]
    - greater [gt]

   It states various lemmas and theorems about natural numbers,
   including Peano's axioms of arithmetic (in Coq, these are provable).
   Case analysis on [nat] and induction on [nat * nat] are provided too
 *)

Require Import Notations.
Require Import Datatypes.
Require Import Logic.
Unset Boxed Definitions.

Open Scope nat_scope.

Definition eq_S := f_equal S.

Hint Resolve (f_equal S): v62.
Hint Resolve (f_equal (A:=nat)): core.

(** The predecessor function *)

Definition pred (n:nat) : nat := match n with
                                 | O => n
                                 | S u => u
                                 end.
Hint Resolve (f_equal pred): v62.

Theorem pred_Sn : forall n:nat, n = pred (S n).
Proof.
  simpl; reflexivity.
Qed.

(** Injectivity of successor *)

Theorem eq_add_S : forall n m:nat, S n = S m -> n = m.
Proof.
  intros n m Sn_eq_Sm.
  replace (n=m) with (pred (S n) = pred (S m)) by auto using pred_Sn.
  rewrite Sn_eq_Sm; trivial.
Qed.

Hint Immediate eq_add_S: core.

Theorem not_eq_S : forall n m:nat, n <> m -> S n <> S m.
Proof.
  red in |- *; auto.
Qed.
Hint Resolve not_eq_S: core.

Definition IsSucc (n:nat) : Prop :=
  match n with
  | O => False
  | S p => True
  end.

(** Zero is not the successor of a number *)

Theorem O_S : forall n:nat, 0 <> S n.
Proof.
  unfold not; intros n H.
  inversion H.
Qed.
Hint Resolve O_S: core.

Theorem n_Sn : forall n:nat, n <> S n.
Proof.
  induction n; auto.
Qed.
Hint Resolve n_Sn: core.

(** Addition *)

Fixpoint plus (n m:nat) {struct n} : nat :=
  match n with
  | O => m
  | S p => S (p + m)
  end

where "n + m" := (plus n m) : nat_scope.

Hint Resolve (f_equal2 plus): v62.
Hint Resolve (f_equal2 (A1:=nat) (A2:=nat)): core.

Lemma plus_n_O : forall n:nat, n = n + 0.
Proof.
  induction n; simpl in |- *; auto.
Qed.
Hint Resolve plus_n_O: core.

Lemma plus_O_n : forall n:nat, 0 + n = n.
Proof.
  auto.
Qed.

Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
Proof.
  intros n m; induction n; simpl in |- *; auto.
Qed.
Hint Resolve plus_n_Sm: core.

Lemma plus_Sn_m : forall n m:nat, S n + m = S (n + m).
Proof.
  auto.
Qed.

(** Standard associated names *)

Notation plus_0_r_reverse := plus_n_O (only parsing).
Notation plus_succ_r_reverse := plus_n_Sm (only parsing).

(** Multiplication *)

Fixpoint mult (n m:nat) {struct n} : nat :=
  match n with
  | O => 0
  | S p => m + p * m
  end

where "n * m" := (mult n m) : nat_scope.

Hint Resolve (f_equal2 mult): core.

Lemma mult_n_O : forall n:nat, 0 = n * 0.
Proof.
  induction n; simpl in |- *; auto.
Qed.
Hint Resolve mult_n_O: core.

Lemma mult_n_Sm : forall n m:nat, n * m + n = n * S m.
Proof.
  intros; induction n as [| p H]; simpl in |- *; auto.
  destruct H; rewrite <- plus_n_Sm; apply (f_equal S).
  pattern m at 1 3 in |- *; elim m; simpl in |- *; auto.
Qed.
Hint Resolve mult_n_Sm: core.

(** Standard associated names *)

Notation mult_0_r_reverse := mult_n_O (only parsing).
Notation mult_succ_r_reverse := mult_n_Sm (only parsing).

(** Truncated subtraction: [m-n] is [0] if [n>=m] *)

Fixpoint minus (n m:nat) {struct n} : nat :=
  match n, m with
  | O, _ => n
  | S k, O => n
  | S k, S l => k - l
  end

where "n - m" := (minus n m) : nat_scope.

(** Definition of the usual orders, the basic properties of [le] and [lt]
    can be found in files Le and Lt *)

Inductive le (n:nat) : nat -> Prop :=
  | le_n : n <= n
  | le_S : forall m:nat, n <= m -> n <= S m

where "n <= m" := (le n m) : nat_scope.

Hint Constructors le: core.
(*i equivalent to : "Hints Resolve le_n le_S : core." i*)

Definition lt (n m:nat) := S n <= m.
Hint Unfold lt: core.

Infix "<" := lt : nat_scope.

Definition ge (n m:nat) := m <= n.
Hint Unfold ge: core.

Infix ">=" := ge : nat_scope.

Definition gt (n m:nat) := m < n.
Hint Unfold gt: core.

Infix ">" := gt : nat_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : nat_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : nat_scope.
Notation "x < y < z" := (x < y /\ y < z) : nat_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : nat_scope.

(** Case analysis *)

Theorem nat_case :
 forall (n:nat) (P:nat -> Prop), P 0 -> (forall m:nat, P (S m)) -> P n.
Proof.
  induction n; auto.
Qed.

(** Principle of double induction *)

Theorem nat_double_ind :
 forall R:nat -> nat -> Prop,
   (forall n:nat, R 0 n) ->
   (forall n:nat, R (S n) 0) ->
   (forall n m:nat, R n m -> R (S n) (S m)) -> forall n m:nat, R n m.
Proof.
  induction n; auto.
  destruct m as [| n0]; auto.
Qed.
