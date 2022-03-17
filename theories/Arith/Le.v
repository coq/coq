(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Order on natural numbers. *)

(** * This file is OBSOLETE, see [Arith_base] instead. *)

Require Export Arith_prebase.


(** * [le] is an order on [nat] *)

#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.le_refl instead.")]
Notation le_refl := Nat.le_refl (only parsing).
#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.le_trans instead.")]
Notation le_trans := Nat.le_trans (only parsing).
#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.le_antisymm instead.")]
Notation le_antisym := Nat.le_antisymm (only parsing).

(** * Properties of [le] w.r.t 0 *)

#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.le_0_l instead.")]
Notation le_0_n := Nat.le_0_l (only parsing).  (* 0 <= n *)
#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.nle_succ_0 instead.")]
Notation le_Sn_0 := Nat.nle_succ_0 (only parsing).  (* ~ S n <= 0 *)
#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use the bidirectional version Nat.le_0_r (with symmetry of equality) instead.")]
Notation le_n_0_eq := Arith_prebase.le_n_0_eq_stt.

(** * Properties of [le] w.r.t successor *)

#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.succ_le_mono instead.")]
Notation le_n_S := Peano.le_n_S (only parsing).
#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.succ_le_mono instead.")]
Notation le_S_n := Peano.le_S_n (only parsing).
#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.le_succ_diag_r instead.")]
Notation le_n_Sn := Nat.le_succ_diag_r (only parsing). (* n <= S n *)
#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.nle_succ_diag_l instead.")]
Notation le_Sn_n := Nat.nle_succ_diag_l (only parsing). (* ~ S n <= n *)
#[local]
Definition le_Sn_le_stt : forall n m, S n <= m -> n <= m := Nat.lt_le_incl.
Opaque le_Sn_le_stt.
#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.lt_le_incl instead.")]
Notation le_Sn_le := le_Sn_le_stt.

(** * Properties of [le] w.r.t predecessor *)

#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.le_pred_l instead.")]
Notation le_pred_n := Nat.le_pred_l (only parsing). (* pred n <= n *)
#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.pred_le_mono instead.")]
Notation le_pred := Nat.pred_le_mono (only parsing). (* n<=m -> pred n <= pred m *)

(** * A different elimination principle for the order on natural numbers *)

#[local]
Definition le_elim_rel_stt :
 forall P:nat -> nat -> Prop,
   (forall p, P 0 p) ->
   (forall p (q:nat), p <= q -> P p q -> P (S p) (S q)) ->
   forall n m, n <= m -> P n m.
Proof.
  intros P H0 HS n.
  induction n; trivial.
  intros m Le. elim Le; intuition.
Qed.
#[deprecated(since="8.16",note="The Arith.Le file is obsolete.")]
Notation le_elim_rel := le_elim_rel_stt.

(* begin hide *)
#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.le_0_l instead.")]
Notation le_O_n := Nat.le_0_l (only parsing).
#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use Nat.nle_succ_0 instead.")]
Notation le_Sn_O := Nat.nle_succ_0 (only parsing).
#[deprecated(since="8.16",note="The Arith.Le file is obsolete. Use the bidirectional version Nat.le_0_r (with symmetry of equality) instead.")]
Notation le_n_O_eq := Arith_prebase.le_n_0_eq_stt.
(* end hide *)
