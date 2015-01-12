(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

Notation le_refl := Nat.le_refl (compat "8.4").
Notation le_trans := Nat.le_trans (compat "8.4").
Notation le_antisym := Nat.le_antisymm (compat "8.4").

Hint Resolve le_trans: arith v62.
Hint Immediate le_antisym: arith v62.

(** * Properties of [le] w.r.t 0 *)

Notation le_0_n := Nat.le_0_l (compat "8.4").  (* 0 <= n *)
Notation le_Sn_0 := Nat.nle_succ_0 (compat "8.4").  (* ~ S n <= 0 *)

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

Notation le_n_Sn := Nat.le_succ_diag_r (compat "8.4"). (* n <= S n *)
Notation le_Sn_n := Nat.nle_succ_diag_l (compat "8.4"). (* ~ S n <= n *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof Nat.lt_le_incl.

Hint Resolve le_0_n le_Sn_0: arith v62.
Hint Resolve le_n_S le_n_Sn le_Sn_n : arith v62.
Hint Immediate le_n_0_eq le_Sn_le le_S_n : arith v62.

(** * Properties of [le] w.r.t predecessor *)

Notation le_pred_n := Nat.le_pred_l (compat "8.4"). (* pred n <= n *)
Notation le_pred := Nat.pred_le_mono (compat "8.4"). (* n<=m -> pred n <= pred m *)

Hint Resolve le_pred_n: arith v62.

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
