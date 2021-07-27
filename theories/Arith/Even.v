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
    Please consider instead predicates [Nat.Even] and [Nat.Odd]
    and Boolean functions [Nat.even] and [Nat.odd]. *)

(** Here we define the predicates [even] and [odd] by mutual induction
    and we prove the decidability and the exclusion of those predicates.
    The main results about parity are proved in the module Div2. *)

Require Import PeanoNat.

Local Open Scope nat_scope.

Implicit Types m n : nat.


(** * Inductive definition of [even] and [odd] *)

Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
    odd_S : forall n, even n -> odd (S n).

#[global]
Hint Constructors even: arith.
#[global]
Hint Constructors odd: arith.

(** * Equivalence with predicates [Nat.Even] and [Nat.odd] *)

#[local]
Definition even_equiv_stt : forall n, even n <-> Nat.Even n.
Proof.
 fix even_equiv 1.
 intros n; destruct n as [|[|n]]; simpl.
 - split; [now exists 0 | constructor].
 - split.
   + inversion_clear 1 as [|? H0]. inversion_clear H0.
   + now rewrite <- Nat.even_spec.
 - rewrite Nat.Even_succ_succ, <- even_equiv.
   split.
   + inversion_clear 1 as [|? H0]. now inversion_clear H0.
   + now do 2 constructor.
Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_equiv := even_equiv_stt.

#[local]
Definition odd_equiv_stt : forall n, odd n <-> Nat.Odd n.
Proof.
 fix odd_equiv 1.
 intros n; destruct n as [|[|n]]; simpl.
 - split.
   + inversion_clear 1.
   + now rewrite <- Nat.odd_spec.
 - split; [ now exists 0 | do 2 constructor ].
 - rewrite Nat.Odd_succ_succ, <- odd_equiv.
   split.
   + inversion_clear 1 as [? H0]. now inversion_clear H0.
   + now do 2 constructor.
Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation odd_equiv := odd_equiv_stt.

(** Basic facts *)

#[local]
Definition even_or_odd_stt n : even n \/ odd n.
Proof.
  induction n as [|n IHn].
  - auto with arith.
  - elim IHn; auto with arith.
Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_or_Odd instead.")]
Notation even_or_odd := even_or_odd_stt.

#[local]
Definition even_odd_dec_stt n : {even n} + {odd n}.
Proof.
  induction n as [|n IHn].
  - auto with arith.
  - elim IHn; auto with arith.
Defined.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_odd_dec := even_odd_dec_stt.

#[local]
Definition not_even_and_odd_stt n : even n -> odd n -> False.
Proof.
  induction n.
  - intros Ev Od. inversion Od.
  - intros Ev Od. inversion Ev. inversion Od. auto with arith.
Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_Odd_False instead.")]
Notation not_even_and_odd := not_even_and_odd_stt (only parsing).


(** * Facts about [even] & [odd] wrt. [plus] *)

#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Ltac parity2bool :=
 rewrite ?even_equiv_stt, ?odd_equiv_stt, <- ?Nat.even_spec, <- ?Nat.odd_spec.

#[local]
Ltac parity2bool_dep :=
 rewrite ?even_equiv_stt, ?odd_equiv_stt, <- ?Nat.even_spec, <- ?Nat.odd_spec.

#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Ltac parity_binop_spec :=
 rewrite ?Nat.even_add, ?Nat.odd_add, ?Nat.even_mul, ?Nat.odd_mul.

#[local]
Ltac parity_binop_spec_dep :=
 rewrite ?Nat.even_add, ?Nat.odd_add, ?Nat.even_mul, ?Nat.odd_mul.

#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Ltac parity_binop :=
 parity2bool_dep; parity_binop_spec_dep; unfold Nat.odd;
 do 2 destruct Nat.even; simpl; tauto.

#[local]
Ltac parity_binop_dep :=
 parity2bool_dep; parity_binop_spec_dep; unfold Nat.odd;
 do 2 destruct Nat.even; simpl; tauto.

#[local]
Definition even_plus_split_stt n m :
  even (n + m) -> even n /\ even m \/ odd n /\ odd m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_plus_split := even_plus_split_stt.

#[local]
Definition odd_plus_split_stt n m :
  odd (n + m) -> odd n /\ even m \/ even n /\ odd m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation odd_plus_split := odd_plus_split_stt.

#[local]
Definition even_even_plus_stt n m: even n -> even m -> even (n + m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_even_plus := even_even_plus_stt.

#[local]
Definition odd_plus_l_stt n m : odd n -> even m -> odd (n + m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation odd_plus_l := odd_plus_l_stt.

#[local]
Definition odd_plus_r_stt n m : even n -> odd m -> odd (n + m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation odd_plus_r := odd_plus_r_stt.

#[local]
Definition odd_even_plus_stt n m : odd n -> odd m -> even (n + m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation odd_even_plus := odd_even_plus_stt.

#[local]
Definition even_plus_aux_stt n m :
    (odd (n + m) <-> odd n /\ even m \/ even n /\ odd m) /\
    (even (n + m) <-> even n /\ even m \/ odd n /\ odd m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_plus_aux := even_plus_aux_stt.

#[local]
Definition even_plus_even_inv_r_stt n m : even (n + m) -> even n -> even m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_plus_even_inv_r := even_plus_even_inv_r_stt.

#[local]
Definition even_plus_even_inv_l_stt n m : even (n + m) -> even m -> even n.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_plus_even_inv_l := even_plus_even_inv_l_stt.

#[local]
Definition even_plus_odd_inv_r_stt n m : even (n + m) -> odd n -> odd m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_plus_odd_inv_r := even_plus_odd_inv_r_stt.

#[local]
Definition even_plus_odd_inv_l_stt n m : even (n + m) -> odd m -> odd n.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_plus_odd_inv_l := even_plus_odd_inv_l_stt.

#[local]
Definition odd_plus_even_inv_l_stt n m : odd (n + m) -> odd m -> even n.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation odd_plus_even_inv_l := odd_plus_even_inv_l_stt.

#[local]
Definition odd_plus_even_inv_r_stt n m : odd (n + m) -> odd n -> even m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation odd_plus_even_inv_r := odd_plus_even_inv_r_stt.

#[local]
Definition odd_plus_odd_inv_l_stt n m : odd (n + m) -> even m -> odd n.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation odd_plus_odd_inv_l := odd_plus_odd_inv_l_stt.

#[local]
Definition odd_plus_odd_inv_r_stt n m : odd (n + m) -> even n -> odd m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation odd_plus_odd_inv_r := odd_plus_odd_inv_r_stt.


(** * Facts about [even] and [odd] wrt. [mult] *)

#[local]
Definition even_mult_aux_stt n m :
  (odd (n * m) <-> odd n /\ odd m) /\ (even (n * m) <-> even n \/ even m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_mult_aux := even_mult_aux_stt.

#[local]
Definition even_mult_l_stt n m : even n -> even (n * m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_mult_l := even_mult_l_stt.

#[local]
Definition even_mult_r_stt n m : even m -> even (n * m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_mult_r := even_mult_r_stt.

#[local]
Definition even_mult_inv_r_stt n m : even (n * m) -> odd n -> even m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_mult_inv_r := even_mult_inv_r_stt.

#[local]
Definition even_mult_inv_l_stt n m : even (n * m) -> odd m -> even n.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation even_mult_inv_l := even_mult_inv_l_stt.

#[local]
Definition odd_mult_stt n m : odd n -> odd m -> odd (n * m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation odd_mult := odd_mult_stt.

#[local]
Definition odd_mult_inv_l_stt n m : odd (n * m) -> odd n.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation odd_mult_inv_l := odd_mult_inv_l_stt.

#[local]
Definition odd_mult_inv_r_stt n m : odd (n * m) -> odd m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Notation odd_mult_inv_r := odd_mult_inv_r_stt.

#[global]
Hint Resolve
 even_even_plus_stt odd_even_plus_stt odd_plus_l_stt odd_plus_r_stt
 even_mult_l_stt even_mult_r_stt even_mult_l_stt even_mult_r_stt odd_mult_stt : arith.
