(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Nota : this file is OBSOLETE, and left only for compatibility.
    Please consider using [Nat.div2] directly, and results about it
    (see file PeanoNat). *)

Require Import PeanoNat Even.

Local Open Scope nat_scope.

Implicit Type n : nat.

(** Here we define [n/2] and prove some of its properties *)

#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete. Use Nat.div2 instead.")]
Notation div2 := Nat.div2 (only parsing).

(** Since [div2] is recursively defined on [0], [1] and [(S (S n))], it is
    useful to prove the corresponding induction principle *)

#[local]
Definition ind_0_1_SS_stt :
  forall P:nat -> Prop,
    P 0 -> P 1 -> (forall n, P n -> P (S (S n))) -> forall n, P n.
Proof.
  intros P H0 H1 H2.
  fix ind_0_1_SS 1.
  intros n; destruct n as [|[|n]].
  - exact H0.
  - exact H1.
  - apply H2, ind_0_1_SS.
Qed.
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete.")]
Notation ind_0_1_SS := ind_0_1_SS_stt.

(** [0 <n  =>  n/2 < n] *)

#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete. Use Nat.lt_div2 instead.")]
Notation lt_div2 := Nat.lt_div2 (only parsing).

#[global]
Hint Resolve Nat.lt_div2: arith.

(** Properties related to the parity *)

#[local]
Definition even_div2_stt n : even n -> Nat.div2 n = Nat.div2 (S n).
Proof.
 rewrite Even.even_equiv_stt. intros (p,->).
 rewrite Nat.div2_succ_double. apply Nat.div2_double.
Qed.
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete.")]
Notation even_div2 := even_div2_stt.

#[local]
Definition odd_div2_stt n : odd n -> S (Nat.div2 n) = Nat.div2 (S n).
Proof.
 rewrite Even.odd_equiv_stt. intros (p,->).
 rewrite Nat.add_1_r, Nat.div2_succ_double.
 simpl. f_equal. symmetry. apply Nat.div2_double.
Qed.
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete.")]
Notation odd_div2 := odd_div2_stt.

#[local]
Definition div2_even_stt n : Nat.div2 n = Nat.div2 (S n) -> even n.
Proof.
 destruct (Even.even_or_odd_stt n) as [Ev|Od]; trivial.
 apply odd_div2_stt in Od. rewrite <- Od. intro Od'.
 elim (n_Sn _ Od').
Qed.
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete.")]
Notation div2_even := div2_even_stt.

#[local]
Definition div2_odd_stt n : S (Nat.div2 n) = Nat.div2 (S n) -> odd n.
Proof.
 destruct (Even.even_or_odd_stt n) as [Ev|Od]; trivial.
 apply even_div2_stt in Ev. rewrite <- Ev. intro Ev'.
 symmetry in Ev'. elim (n_Sn _ Ev').
Qed.
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete.")]
Notation div2_odd := div2_odd_stt.

#[global]
Hint Resolve even_div2_stt div2_even_stt odd_div2_stt div2_odd_stt: arith.

#[local]
Definition even_odd_div2_stt n :
 (even n <-> Nat.div2 n = Nat.div2 (S n)) /\
 (odd n <-> S (Nat.div2 n) = Nat.div2 (S n)).
Proof.
 split; split; auto using div2_odd_stt, div2_even_stt, odd_div2_stt, even_div2_stt.
Qed.
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete.")]
Notation even_odd_div2 := even_odd_div2_stt.



(** Properties related to the double ([2n]) *)

#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete. Use Nat.double instead.")]
Notation double := Nat.double (only parsing).

#[global]
Hint Unfold Nat.double: arith.

#[local]
Definition double_S_stt : forall n, Nat.double (S n) = S (S (Nat.double n))
                        := fun n => Nat.add_succ_r (S n) n.
Opaque double_S_stt.
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete. Use Nat.add_succ_r instead.")]
Notation double_S := double_S_stt.

#[local]
Definition double_plus_stt : forall n m, Nat.double (n + m) = Nat.double n + Nat.double m
                           := fun n m => Nat.add_shuffle1 n m n m.
Opaque double_plus_stt.
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete. Use Nat.add_shuffle1 instead.")]
Notation double_plus := double_plus_stt.

#[global]
Hint Resolve double_S_stt: arith.

#[local]
Definition even_odd_double_stt n :
  (even n <-> n = Nat.double (Nat.div2 n)) /\ (odd n <-> n = S (Nat.double (Nat.div2 n))).
Proof.
  revert n. fix even_odd_double 1. intros n; destruct n as [|[|n]].
  - (* n = 0 *)
    split; split; auto with arith. inversion 1.
  - (* n = 1 *)
    split; split; auto with arith. inversion_clear 1 as [|? H0]. inversion H0.
  - (* n = (S (S n')) *)
    destruct (even_odd_double n) as ((Ev,Ev'),(Od,Od')).
    split; split; simpl Nat.div2; rewrite ?double_S_stt.
    + inversion_clear 1 as [|? H0]. inversion_clear H0. auto.
    + injection 1. auto with arith.
    + inversion_clear 1 as [? H0]. inversion_clear H0. auto.
    + injection 1. auto with arith.
Qed.
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete.")]
Notation even_odd_double := even_odd_double_stt.

(** Specializations *)

#[local]
Definition even_double_stt n : even n -> n = Nat.double (Nat.div2 n).
Proof proj1 (proj1 (even_odd_double_stt n)).
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete.")]
Notation even_double := even_double_stt.

#[local]
Definition double_even_stt n : n = Nat.double (Nat.div2 n) -> even n.
Proof proj2 (proj1 (even_odd_double_stt n)).
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete.")]
Notation double_even := double_even_stt.

#[local]
Definition odd_double_stt n : odd n -> n = S (Nat.double (Nat.div2 n)).
Proof proj1 (proj2 (even_odd_double_stt n)).
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete.")]
Notation odd_double := odd_double_stt.

#[local]
Definition double_odd_stt n : n = S (Nat.double (Nat.div2 n)) -> odd n.
Proof proj2 (proj2 (even_odd_double_stt n)).
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete.")]
Notation double_odd := double_odd_stt.

#[global]
Hint Resolve even_double_stt double_even_stt odd_double_stt double_odd_stt: arith.

(** Application:
    - if [n] is even then there is a [p] such that [n = 2p]
    - if [n] is odd  then there is a [p] such that [n = 2p+1]

    (Immediate: it is [n/2]) *)

#[local]
Definition even_2n_stt : forall n, even n -> {p : nat | n = Nat.double p}.
Proof.
  intros n H. exists (Nat.div2 n). auto with arith.
Defined.
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete.")]
Notation even_2n := even_2n_stt.

#[local]
Definition odd_S2n_stt : forall n, odd n -> {p : nat | n = S (Nat.double p)}.
Proof.
  intros n H. exists (Nat.div2 n). auto with arith.
Defined.
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete.")]
Notation odd_S2n := odd_S2n_stt.

(** Doubling before dividing by two brings back to the initial number. *)

#[local]
Definition div2_double_stt n : Nat.div2 (2*n) = n.
Proof. apply Nat.div2_double. Qed.
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete. Use Nat.div2_double instead.")]
Notation div2_double := div2_double_stt.

#[local]
Definition div2_double_plus_one_stt n : Nat.div2 (S (2*n)) = n.
Proof. apply Nat.div2_succ_double. Qed.
#[deprecated(since="8.16",note="The Arith.Div2 file is obsolete. Use Nat.div2_succ_double instead.")]
Notation div2_double_plus_one := div2_double_plus_one_stt.
