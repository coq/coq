(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Natural numbers [nat] built from [O] and [S] are defined in Datatypes.v *)

(** This module defines the following operations on natural numbers :
    - predecessor [pred]
    - addition [plus]
    - multiplication [mult]
    - less or equal order [le]
    - less [lt]
    - greater or equal [ge]
    - greater [gt]

   This module states various lemmas and theorems about natural numbers,
   including Peano's axioms of arithmetic (in Coq, these are in fact provable)
   Case analysis on [nat] and induction on [nat * nat] are provided too *)

Require Import Notations.
Require Import Datatypes.
Require Import Logic.

Open Scope nat_scope.

Definition eq_S := f_equal S.

Hint Resolve (f_equal S): v62.
Hint Resolve (f_equal (A:=nat)): core.

(** The predecessor function *)

Definition pred (n:nat) : nat := match n with
                                 | O => 0
                                 | S u => u
                                 end.
Hint Resolve (f_equal pred): v62.

Theorem pred_Sn : forall n:nat, n = pred (S n).
Proof.
  auto.
Qed.

Theorem eq_add_S : forall n m:nat, S n = S m -> n = m.
Proof.
  intros n m H; change (pred (S n) = pred (S m)) in |- *; auto.
Qed.

Hint Immediate eq_add_S: core v62.

(** A consequence of the previous axioms *)

Theorem not_eq_S : forall n m:nat, n <> m -> S n <> S m.
Proof.
  red in |- *; auto.
Qed.
Hint Resolve not_eq_S: core v62.

Definition IsSucc (n:nat) : Prop :=
  match n with
  | O => False
  | S p => True
  end.


Theorem O_S : forall n:nat, 0 <> S n.
Proof.
  red in |- *; intros n H.
  change (IsSucc 0) in |- *.
  rewrite <- (sym_eq (x:=0) (y:=(S n))); [ exact I | assumption ].
Qed.
Hint Resolve O_S: core v62.

Theorem n_Sn : forall n:nat, n <> S n.
Proof.
  induction n; auto.
Qed.
Hint Resolve n_Sn: core v62.

(** Addition *)

Fixpoint plus (n m:nat) {struct n} : nat :=
  match n with
  | O => m
  | S p => S (plus p m)
  end.
Hint Resolve (f_equal2 plus): v62.
Hint Resolve (f_equal2 (A1:=nat) (A2:=nat)): core.

Infix "+" := plus : nat_scope.

Lemma plus_n_O : forall n:nat, n = n + 0.
Proof.
  induction n; simpl in |- *; auto.
Qed.
Hint Resolve plus_n_O: core v62.

Lemma plus_O_n : forall n:nat, 0 + n = n.
Proof.
  auto.
Qed.

Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
Proof.
  intros n m; induction n; simpl in |- *; auto.
Qed.
Hint Resolve plus_n_Sm: core v62.

Lemma plus_Sn_m : forall n m:nat, S n + m = S (n + m).
Proof.
  auto.
Qed.

(** Multiplication *)

Fixpoint mult (n m:nat) {struct n} : nat :=
  match n with
  | O => 0
  | S p => m + mult p m
  end.
Hint Resolve (f_equal2 mult): core v62.

Infix "*" := mult : nat_scope.

Lemma mult_n_O : forall n:nat, 0 = n * 0.
Proof.
  induction n; simpl in |- *; auto.
Qed.
Hint Resolve mult_n_O: core v62.

Lemma mult_n_Sm : forall n m:nat, n * m + n = n * S m.
Proof.
  intros; induction n as [| p H]; simpl in |- *; auto.
  destruct H; rewrite <- plus_n_Sm; apply (f_equal S).
  pattern m at 1 3 in |- *; elim m; simpl in |- *; auto.
Qed.
Hint Resolve mult_n_Sm: core v62.

(** Definition of subtraction on [nat] : [m-n] is [0] if [n>=m] *)

Fixpoint minus (n m:nat) {struct n} : nat :=
  match n, m with
  | O, _ => 0
  | S k, O => S k
  | S k, S l => minus k l
  end. 

Infix "-" := minus : nat_scope.

(** Definition of the usual orders, the basic properties of [le] and [lt] 
    can be found in files Le and Lt *)

(** An inductive definition to define the order *)

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m:nat, le n m -> le n (S m).

Infix "<=" := le : nat_scope.

Hint Constructors le: core v62.
(*i equivalent to : "Hints Resolve le_n le_S : core v62." i*)

Definition lt (n m:nat) := S n <= m.
Hint Unfold lt: core v62.

Infix "<" := lt : nat_scope.

Definition ge (n m:nat) := m <= n.
Hint Unfold ge: core v62.

Infix ">=" := ge : nat_scope.

Definition gt (n m:nat) := m < n.
Hint Unfold gt: core v62.

Infix ">" := gt : nat_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : nat_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : nat_scope.
Notation "x < y < z" := (x < y /\ y < z) : nat_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : nat_scope.

(** Pattern-Matching on natural numbers *)

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

(** Notations *)
