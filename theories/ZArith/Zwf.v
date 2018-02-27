(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZArith_base.
Require Export Wf_nat.
Require Import Omega.
Local Open Scope Z_scope.

(** Well-founded relations on Z. *)

(** We define the following family of relations on [Z x Z]:

    [x (Zwf c) y]   iff   [x < y & c <= y]
 *)

Definition Zwf (c x y:Z) := c <= y /\ x < y.

(** and we prove that [(Zwf c)] is well founded *)

Section wf_proof.

  Variable c : Z.

  (** The proof of well-foundness is classic: we do the proof by induction
      on a measure in nat, which is here [|x-c|] *)

  Let f (z:Z) := Z.abs_nat (z - c).

  Lemma Zwf_well_founded : well_founded (Zwf c).
    red; intros.
    assert (forall (n:nat) (a:Z), (f a < n)%nat \/ a < c -> Acc (Zwf c) a).
    clear a; simple induction n; intros.
  (** n= 0 *)
    case H; intros.
    case (lt_n_O (f a)); auto.
    apply Acc_intro; unfold Zwf; intros.
    assert False; omega || contradiction.
  (** inductive case *)
    case H0; clear H0; intro; auto.
    apply Acc_intro; intros.
    apply H.
    unfold Zwf in H1.
    case (Z.le_gt_cases c y); intro; auto with zarith.
    left.
    red in H0.
    apply lt_le_trans with (f a); auto with arith.
    unfold f.
    apply Zabs2Nat.inj_lt; omega.
    apply (H (S (f a))); auto.
  Qed.

End wf_proof.

Hint Resolve Zwf_well_founded: datatypes.


(** We also define the other family of relations:

    [x (Zwf_up c) y]   iff   [y < x <= c]
 *)

Definition Zwf_up (c x y:Z) := y < x <= c.

(** and we prove that [(Zwf_up c)] is well founded *)

Section wf_proof_up.

  Variable c : Z.

  (** The proof of well-foundness is classic: we do the proof by induction
      on a measure in nat, which is here [|c-x|] *)

  Let f (z:Z) := Z.abs_nat (c - z).

  Lemma Zwf_up_well_founded : well_founded (Zwf_up c).
  Proof.
    apply well_founded_lt_compat with (f := f).
    unfold Zwf_up, f.
    intros.
    apply Zabs2Nat.inj_lt; try (apply Z.le_0_sub; intuition).
    now apply Z.sub_lt_mono_l.
  Qed.

End wf_proof_up.

Hint Resolve Zwf_up_well_founded: datatypes.
