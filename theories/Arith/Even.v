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

#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even or Nat.Even_alt instead.")]
Notation even := Nat.Even_alt (only parsing).
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even or Nat.Even_alt instead.")]
Notation odd := Nat.Odd_alt (only parsing).
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even or Nat.Even_alt_O instead.")]
Notation even_O := Nat.Even_alt_O (only parsing).
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even or Nat.Even_alt_S instead.")]
Notation even_S := Nat.Even_alt_S (only parsing).
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even or Nat.Odd_alt_S instead.")]
Notation odd_S := Nat.Odd_alt_S (only parsing).
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even or Nat.Even_alt_ind instead.")]
Notation even_ind := Nat.Even_alt_ind (only parsing).
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even or Nat.Even_alt_sind instead.")]
Notation even_sind := Nat.Even_alt_sind (only parsing).
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even or Nat.Odd_alt_ind instead.")]
Notation odd_ind := Nat.Odd_alt_ind (only parsing).
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even or Nat.Odd_alt_ind instead.")]
Notation odd_sind := Nat.Odd_alt_sind (only parsing).

#[global]
Hint Constructors Nat.Even_alt: arith.
#[global]
Hint Constructors Nat.Odd_alt: arith.

(** * Equivalence with predicates [Nat.Even] and [Nat.odd] *)

#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_alt_Even instead.")]
Notation even_equiv := Nat.Even_alt_Even.

#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Odd_alt_Odd instead")]
Notation odd_equiv := Nat.Odd_alt_Odd.

(** Basic facts *)

#[local]
Definition even_or_odd_stt n : Nat.Even_alt n \/ Nat.Odd_alt n.
Proof.
  induction n as [|n IHn].
  - auto with arith.
  - elim IHn; auto with arith.
Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_or_Odd (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation even_or_odd := even_or_odd_stt.

#[local]
Definition even_odd_dec_stt n : {Nat.Even_alt n} + {Nat.Odd_alt n}.
Proof.
  induction n as [|n IHn].
  - auto with arith.
  - elim IHn; auto with arith.
Defined.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_Odd_dec (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead")]
Notation even_odd_dec := even_odd_dec_stt.

#[local]
Definition not_even_and_odd_stt n : Nat.Even_alt n -> Nat.Odd_alt n -> False.
Proof.
  induction n.
  - intros Ev Od. inversion Od.
  - intros Ev Od. inversion Ev. inversion Od. auto with arith.
Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_Odd_False (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation not_even_and_odd := not_even_and_odd_stt (only parsing).


(** * Facts about [even] & [odd] wrt. [plus] *)

#[deprecated(since="8.16",note="The Arith.Even file is obsolete.")]
Ltac parity2bool :=
 rewrite ?Nat.Even_alt_Even, ?Nat.Odd_alt_Odd, <- ?Nat.even_spec, <- ?Nat.odd_spec.

#[local]
Ltac parity2bool_dep :=
 rewrite ?Nat.Even_alt_Even, ?Nat.Odd_alt_Odd, <- ?Nat.even_spec, <- ?Nat.odd_spec.

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
  Nat.Even_alt (n + m) -> Nat.Even_alt n /\ Nat.Even_alt m \/ Nat.Odd_alt n /\ Nat.Odd_alt m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_add_split (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation even_plus_split := even_plus_split_stt.

#[local]
Definition odd_plus_split_stt n m :
  Nat.Odd_alt (n + m) -> Nat.Odd_alt n /\ Nat.Even_alt m \/ Nat.Even_alt n /\ Nat.Odd_alt m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Odd_add_split (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation odd_plus_split := odd_plus_split_stt.

#[local]
Definition even_even_plus_stt n m: Nat.Even_alt n -> Nat.Even_alt m -> Nat.Even_alt (n + m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_Even_add (together with Nat.Even_alt_Even) instead.")]
Notation even_even_plus := even_even_plus_stt.

#[local]
Definition odd_plus_l_stt n m : Nat.Odd_alt n -> Nat.Even_alt m -> Nat.Odd_alt (n + m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Odd_add_l (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation odd_plus_l := odd_plus_l_stt.

#[local]
Definition odd_plus_r_stt n m : Nat.Even_alt n -> Nat.Odd_alt m -> Nat.Odd_alt (n + m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Odd_add_r (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation odd_plus_r := odd_plus_r_stt.

#[local]
Definition odd_even_plus_stt n m : Nat.Odd_alt n -> Nat.Odd_alt m -> Nat.Even_alt (n + m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Odd_Odd_add instead.")]
Notation odd_even_plus := odd_even_plus_stt.

#[local]
Definition even_plus_aux_stt n m :
    (Nat.Odd_alt (n + m) <-> Nat.Odd_alt n /\ Nat.Even_alt m \/ Nat.Even_alt n /\ Nat.Odd_alt m) /\
    (Nat.Even_alt (n + m) <-> Nat.Even_alt n /\ Nat.Even_alt m \/ Nat.Odd_alt n /\ Nat.Odd_alt m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_add_aux (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation even_plus_aux := even_plus_aux_stt.

#[local]
Definition even_plus_even_inv_r_stt n m : Nat.Even_alt (n + m) -> Nat.Even_alt n -> Nat.Even_alt m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_add_Even_inv_r (together with Nat.Even_alt_Even) instead.")]
Notation even_plus_even_inv_r := even_plus_even_inv_r_stt.

#[local]
Definition even_plus_even_inv_l_stt n m : Nat.Even_alt (n + m) -> Nat.Even_alt m -> Nat.Even_alt n.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_add_Even_inv_l (together with Nat.Even_alt_Even) instead.")]
Notation even_plus_even_inv_l := even_plus_even_inv_l_stt.

#[local]
Definition even_plus_odd_inv_r_stt n m : Nat.Even_alt (n + m) -> Nat.Odd_alt n -> Nat.Odd_alt m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_add_Odd_inv_r (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation even_plus_odd_inv_r := even_plus_odd_inv_r_stt.

#[local]
Definition even_plus_odd_inv_l_stt n m : Nat.Even_alt (n + m) -> Nat.Odd_alt m -> Nat.Odd_alt n.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_add_Even_inv_l (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation even_plus_odd_inv_l := even_plus_odd_inv_l_stt.

#[local]
Definition odd_plus_even_inv_l_stt n m : Nat.Odd_alt (n + m) -> Nat.Odd_alt m -> Nat.Even_alt n.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Odd_add_Even_inv_l (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation odd_plus_even_inv_l := odd_plus_even_inv_l_stt.

#[local]
Definition odd_plus_even_inv_r_stt n m : Nat.Odd_alt (n + m) -> Nat.Odd_alt n -> Nat.Even_alt m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Odd_add_Even_inv_r (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation odd_plus_even_inv_r := odd_plus_even_inv_r_stt.

#[local]
Definition odd_plus_odd_inv_l_stt n m : Nat.Odd_alt (n + m) -> Nat.Even_alt m -> Nat.Odd_alt n.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Odd_add_Odd_inv_l (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation odd_plus_odd_inv_l := odd_plus_odd_inv_l_stt.

#[local]
Definition odd_plus_odd_inv_r_stt n m : Nat.Odd_alt (n + m) -> Nat.Even_alt n -> Nat.Odd_alt m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Odd_add_Odd_inv_r (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation odd_plus_odd_inv_r := odd_plus_odd_inv_r_stt.


(** * Facts about [even] and [odd] wrt. [mult] *)

#[local]
Definition even_mult_aux_stt n m :
  (Nat.Odd_alt (n * m) <-> Nat.Odd_alt n /\ Nat.Odd_alt m) /\ (Nat.Even_alt (n * m) <-> Nat.Even_alt n \/ Nat.Even_alt m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_mul_aux (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation even_mult_aux := even_mult_aux_stt.

#[local]
Definition even_mult_l_stt n m : Nat.Even_alt n -> Nat.Even_alt (n * m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_mul_l (together with Nat.Even_alt_Even) instead.")]
Notation even_mult_l := even_mult_l_stt.

#[local]
Definition even_mult_r_stt n m : Nat.Even_alt m -> Nat.Even_alt (n * m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_mul_r (together with Nat.Even_alt_Even) instead.")]
Notation even_mult_r := even_mult_r_stt.

#[local]
Definition even_mult_inv_r_stt n m : Nat.Even_alt (n * m) -> Nat.Odd_alt n -> Nat.Even_alt m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_mul_inv_r (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation even_mult_inv_r := even_mult_inv_r_stt.

#[local]
Definition even_mult_inv_l_stt n m : Nat.Even_alt (n * m) -> Nat.Odd_alt m -> Nat.Even_alt n.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Even_mul_inv_l (together with Nat.Even_alt_Even and Nat.Odd_alt_Odd) instead.")]
Notation even_mult_inv_l := even_mult_inv_l_stt.

#[local]
Definition odd_mult_stt n m : Nat.Odd_alt n -> Nat.Odd_alt m -> Nat.Odd_alt (n * m).
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Odd_mul (together with Nat.Odd_alt_Odd) instead.")]
Notation odd_mult := odd_mult_stt.

#[local]
Definition odd_mult_inv_l_stt n m : Nat.Odd_alt (n * m) -> Nat.Odd_alt n.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Odd_mul_inv_l (together with Nat.Odd_alt_Odd) instead.")]
Notation odd_mult_inv_l := odd_mult_inv_l_stt.

#[local]
Definition odd_mult_inv_r_stt n m : Nat.Odd_alt (n * m) -> Nat.Odd_alt m.
Proof. parity_binop_dep. Qed.
#[deprecated(since="8.16",note="The Arith.Even file is obsolete. Use Nat.Odd_mul_inv_r (together with Nat.Odd_alt_Odd) instead.")]
Notation odd_mult_inv_r := odd_mult_inv_r_stt.

#[global]
Hint Resolve
 even_even_plus_stt odd_even_plus_stt odd_plus_l_stt odd_plus_r_stt
 even_mult_l_stt even_mult_r_stt even_mult_l_stt even_mult_r_stt odd_mult_stt : arith.
