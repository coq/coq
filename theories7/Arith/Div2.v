(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Lt.
Require Plus.
Require Compare_dec.
Require Even.

V7only [Import nat_scope.].
Open Local Scope nat_scope.

Implicit Variables Type n:nat.

(** Here we define [n/2] and prove some of its properties *)

Fixpoint div2 [n:nat] : nat :=
  Cases n of
    O => O
  | (S O) => O
  | (S (S n')) => (S (div2 n'))
  end.

(** Since [div2] is recursively defined on [0], [1] and [(S (S n))], it is
    useful to prove the corresponding induction principle *)

Lemma ind_0_1_SS : (P:nat->Prop)
  (P O) -> (P (S O)) -> ((n:nat)(P n)->(P (S (S n)))) -> (n:nat)(P n).
Proof.
Intros.
Cut (n:nat)(P n)/\(P (S n)).
Intros. Elim (H2 n). Auto with arith.

NewInduction n0. Auto with arith.
Intros. Elim IHn0; Auto with arith.
Qed.

(** [0 <n  =>  n/2 < n] *)

Lemma lt_div2 : (n:nat) (lt O n) -> (lt (div2 n) n).
Proof.
Intro n. Pattern n. Apply ind_0_1_SS.
Intro. Inversion H.
Auto with arith.
Intros. Simpl.
Case (zerop n0).
Intro. Rewrite e. Auto with arith.
Auto with arith.
Qed.

Hints Resolve lt_div2 : arith.

(** Properties related to the parity *)

Lemma even_odd_div2 : (n:nat) 
  ((even n)<->(div2 n)=(div2 (S n))) /\ ((odd n)<->(S (div2 n))=(div2 (S n))).
Proof.
Intro n. Pattern n. Apply ind_0_1_SS.
(* n  = 0 *)
Split. Split; Auto with arith. 
Split. Intro H. Inversion H.
Intro H.  Absurd (S (div2 O))=(div2 (S O)); Auto with arith.
(* n = 1 *)
Split. Split. Intro. Inversion H. Inversion H1.
Intro H.  Absurd (div2 (S O))=(div2 (S (S O))).
Simpl. Discriminate. Assumption.
Split; Auto with arith.
(* n = (S (S n')) *)
Intros. Decompose [and] H. Unfold iff in H0 H1.
Decompose [and] H0. Decompose [and] H1. Clear H H0 H1.
Split; Split; Auto with arith.
Intro H. Inversion H. Inversion H1.
Change (S (div2 n0))=(S (div2 (S n0))). Auto with arith.
Intro H. Inversion H. Inversion H1.
Change (S (S (div2 n0)))=(S (div2 (S n0))). Auto with arith.
Qed.

(** Specializations *)

Lemma even_div2 : (n:nat) (even n) -> (div2 n)=(div2 (S n)).
Proof [n:nat](proj1 ? ? (proj1 ? ? (even_odd_div2 n))).

Lemma div2_even : (n:nat) (div2 n)=(div2 (S n)) -> (even n).
Proof [n:nat](proj2 ? ? (proj1 ? ? (even_odd_div2 n))).

Lemma odd_div2 : (n:nat) (odd n) -> (S (div2 n))=(div2 (S n)).
Proof [n:nat](proj1 ? ? (proj2 ? ? (even_odd_div2 n))).

Lemma div2_odd : (n:nat) (S (div2 n))=(div2 (S n)) -> (odd n).
Proof [n:nat](proj2 ? ? (proj2 ? ? (even_odd_div2 n))).

Hints Resolve even_div2 div2_even odd_div2 div2_odd : arith.

(** Properties related to the double ([2n]) *)

Definition double := [n:nat](plus n n).

Hints Unfold double : arith.

Lemma double_S : (n:nat) (double (S n))=(S (S (double n))).
Proof.
Intro. Unfold double. Simpl. Auto with arith.
Qed.

Lemma double_plus : (m,n:nat) (double (plus m n))=(plus (double m) (double n)).
Proof.
Intros m n. Unfold double.
Do 2 Rewrite -> plus_assoc_r. Rewrite -> (plus_permute n).
Reflexivity.
Qed.

Hints Resolve double_S : arith.

Lemma even_odd_double : (n:nat) 
  ((even n)<->n=(double (div2 n))) /\ ((odd n)<->n=(S (double (div2 n)))).
Proof.
Intro n. Pattern n. Apply ind_0_1_SS.
(* n = 0 *)
Split; Split; Auto with arith.
Intro H. Inversion H.
(* n = 1 *)
Split; Split; Auto with arith.
Intro H. Inversion H. Inversion H1.
(* n = (S (S n')) *)
Intros. Decompose [and] H. Unfold iff in H0 H1.
Decompose [and] H0. Decompose [and] H1. Clear H H0 H1.
Split; Split.
Intro H. Inversion H. Inversion H1.
Simpl. Rewrite (double_S (div2 n0)). Auto with arith.
Simpl. Rewrite (double_S (div2 n0)). Intro H. Injection H. Auto with arith.
Intro H. Inversion H. Inversion H1.
Simpl. Rewrite (double_S (div2 n0)). Auto with arith.
Simpl. Rewrite (double_S (div2 n0)). Intro H. Injection H. Auto with arith.
Qed.


(** Specializations *)

Lemma even_double : (n:nat) (even n) -> n=(double (div2 n)).
Proof [n:nat](proj1 ? ? (proj1 ? ? (even_odd_double n))).

Lemma double_even : (n:nat) n=(double (div2 n)) -> (even n).
Proof [n:nat](proj2 ? ? (proj1 ? ? (even_odd_double n))).

Lemma odd_double : (n:nat) (odd n) -> n=(S (double (div2 n))).
Proof [n:nat](proj1 ? ? (proj2 ? ? (even_odd_double n))).

Lemma double_odd : (n:nat) n=(S (double (div2 n))) -> (odd n).
Proof [n:nat](proj2 ? ? (proj2 ? ? (even_odd_double n))).

Hints Resolve even_double double_even odd_double double_odd : arith.

(** Application: 
    - if [n] is even then there is a [p] such that [n = 2p]
    - if [n] is odd  then there is a [p] such that [n = 2p+1]

    (Immediate: it is [n/2]) *)

Lemma even_2n : (n:nat) (even n) -> { p:nat | n=(double p) }.
Proof.
Intros n H. Exists (div2 n). Auto with arith.
Qed.

Lemma odd_S2n : (n:nat) (odd n) -> { p:nat | n=(S (double p)) }.
Proof.
Intros n H. Exists (div2 n). Auto with arith.
Qed.

