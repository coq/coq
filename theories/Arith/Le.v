(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Order on natural numbers.

 This file is mostly OBSOLETE now, see module [PeanoNat.Nat] instead.

 [le] is defined in [Init/Peano.v] as:
<<
Inductive le (n:nat) : nat -> Prop :=
  | le_n : n <= n
  | le_S : forall m:nat, n <= m -> n <= S m

where "n <= m" := (le n m) : nat_scope.
>>
*)

Require Import PeanoNat.

Local Open Scope nat_scope.

(** * [le] is an order on [nat] *)

Notation le_refl := Nat.le_refl (only parsing).
Notation le_trans := Nat.le_trans (only parsing).
Notation le_antisym := Nat.le_antisymm (only parsing).

Hint Resolve le_trans: arith.
Hint Immediate le_antisym: arith.

(** * Properties of [le] w.r.t 0 *)

Notation le_0_n := Nat.le_0_l (only parsing).  (* 0 <= n *)
Notation le_Sn_0 := Nat.nle_succ_0 (only parsing).  (* ~ S n <= 0 *)

Lemma le_n_0_eq n : n <= 0 -> 0 = n.
Proof.
 intros. symmetry. now apply Nat.le_0_r.
Qed.

(** * Properties of [le] w.r.t successor *)

(** See also [Nat.succ_le_mono]. *)

Theorem le_n_S : forall n m, n <= m -> S n <= S m.
Proof Peano.le_n_S.

Theorem le_S_n : forall n m, S n <= S m -> n <= m.
Proof Peano.le_S_n.

Notation le_n_Sn := Nat.le_succ_diag_r (only parsing). (* n <= S n *)
Notation le_Sn_n := Nat.nle_succ_diag_l (only parsing). (* ~ S n <= n *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof Nat.lt_le_incl.

Hint Resolve le_0_n le_Sn_0: arith.
Hint Resolve le_n_S le_n_Sn le_Sn_n : arith.
Hint Immediate le_n_0_eq le_Sn_le le_S_n : arith.

(** * Properties of [le] w.r.t predecessor *)

Notation le_pred_n := Nat.le_pred_l (only parsing). (* pred n <= n *)
Notation le_pred := Nat.pred_le_mono (only parsing). (* n<=m -> pred n <= pred m *)

Hint Resolve le_pred_n: arith.

(** * A different elimination principle for the order on natural numbers *)

Lemma le_elim_rel :
 forall P:nat -> nat -> Prop,
   (forall p, P 0 p) ->
   (forall p (q:nat), p <= q -> P p q -> P (S p) (S q)) ->
   forall n m, n <= m -> P n m.
Proof.
  intros P H0 HS.
  induction n; trivial.
  intros m Le. elim Le; auto with arith.
 Qed.

(* begin hide *)
Notation le_O_n := le_0_n (only parsing).
Notation le_Sn_O := le_Sn_0 (only parsing).
Notation le_n_O_eq := le_n_0_eq (only parsing).
(* end hide *)
