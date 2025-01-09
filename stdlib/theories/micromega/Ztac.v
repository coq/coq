(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Attributes deprecated(since="9.0", note="use lia instead").
Local Set Warnings "-deprecated".

(** Tactics for doing arithmetic proofs.
    Useful to bootstrap lia.
 *)

Require Import BinInt.
Require Import (ltac.notations) Ring_tac.
Local Open Scope Z_scope.

#[deprecated(use=Z.eq_le_incl, since="9.0")]
Lemma eq_incl :
  forall (x y:Z), x = y -> x <= y /\ y <= x.
Proof. split; apply Z.eq_le_incl; auto 1 using eq_sym. Qed.

#[deprecated(use=Z.lt_trichotomy, since="9.0")]
Lemma elim_concl_eq :
  forall x y, (x < y \/ y < x -> False) -> x = y.
Proof. intros; pose proof Z.lt_trichotomy x y; intuition idtac. Qed.

#[deprecated(use=Z.nlt_ge, since="9.0")]
Lemma elim_concl_le :
  forall x y, (y < x -> False) -> x <= y.
Proof. intros *. apply Z.nlt_ge. Qed.

#[deprecated(use=Z.nle_gt, since="9.0")]
Lemma elim_concl_lt :
  forall x y, (y <= x -> False) -> x < y.
Proof. intros *. apply Z.nle_gt. Qed.

#[deprecated(use=Z.le_succ_l, since="9.0")]
Lemma Zlt_le_add_1 : forall n m : Z, n < m -> n + 1 <= m.
Proof. apply Z.le_succ_l. Qed.

#[deprecated(since="9.0")]
Local Lemma Private_Zle_minus_le_0 n m : m <= n -> 0 <= n - m.
Proof.
 apply Z.le_0_sub.
Qed.

#[deprecated(since="9.0")]
Ltac normZ :=
  repeat
  match goal with
  | H : _ < _ |- _ =>  apply Zlt_le_add_1 in H
  | H : ?Y <= _ |- _ =>
    lazymatch Y with
    | 0 => fail
    | _ => apply Private_Zle_minus_le_0 in H
    end
  | H : _ >= _ |- _ => apply Z.ge_le in H
  | H : _ > _  |- _ => apply Z.gt_lt in H
  | H : _ = _  |- _ => apply eq_incl in H ; destruct H
  | |- @eq Z _ _  => apply elim_concl_eq ; let H := fresh "HZ" in intros [H|H]
  | |- _ <= _ => apply elim_concl_le ; intros
  | |- _ < _ => apply elim_concl_lt ; intros
  | |- _ >= _ => apply Z.le_ge
  end.

Inductive proof_deprecated :=
| Hyp_deprecated (e : Z) (prf : 0 <= e)
| Add_deprecated (p1 p2: proof_deprecated)
| Mul_deprecated (p1 p2: proof_deprecated)
| Cst_deprecated (c : Z)
.

#[deprecated(since="9.0")]
Notation proof := proof_deprecated (only parsing).
#[deprecated(since="9.0")]
Notation Hyp := Hyp_deprecated (only parsing).
#[deprecated(since="9.0")]
Notation Add := Add_deprecated (only parsing).
#[deprecated(since="9.0")]
Notation Mul := Mul_deprecated (only parsing).
#[deprecated(since="9.0")]
Notation Cst := Cst_deprecated (only parsing).

#[deprecated(use=Z.add_nonneg_nonneg, since="9.0")]
Lemma add_le : forall e1 e2, 0 <= e1 -> 0 <= e2 -> 0 <= e1+e2.
Proof. apply Z.add_nonneg_nonneg. Qed.

#[deprecated(use=Z.mul_nonneg_nonneg, since="9.0")]
Lemma mul_le : forall e1 e2, 0 <= e1 -> 0 <= e2 -> 0 <= e1*e2.
Proof. apply Z.mul_nonneg_nonneg. Qed.

#[deprecated(since="9.0")]
Local Definition Private_Z_le_dec x y : {x <= y} + {~ x <= y}.
Proof.
  unfold Z.le; case Z.compare; (now left) || (right; tauto).
Defined.

#[deprecated(since="9.0")]
Fixpoint eval_proof (p : proof) : { e : Z | 0 <= e} :=
  match p with
  | Hyp e prf => exist _ e prf
  | Add p1 p2 => let (e1,p1) := eval_proof p1 in
                 let (e2,p2) := eval_proof p2 in
                 exist _ _ (add_le _ _ p1 p2)
  | Mul p1 p2  => let (e1,p1) := eval_proof p1 in
                 let (e2,p2) := eval_proof p2 in
                 exist _ _ (mul_le _ _ p1 p2)
  | Cst c      =>  match Private_Z_le_dec 0 c with
                   | left prf => exist _ _ prf
                   |  _       => exist _ _ Z.le_0_1
                 end
  end.

#[deprecated(since="9.0")]
Ltac lia_step p :=
  let H := fresh in
  let prf := (eval cbn - [Z.le Z.mul Z.opp Z.sub Z.add] in (eval_proof p)) in
  match prf with
  | @exist _ _ _ ?P =>  pose proof P as H
  end ; ring_simplify in H.

#[deprecated(since="9.0")]
Ltac lia_contr :=
  match goal with
  | H : 0 <= - (Zpos _) |- _ =>
    rewrite <- Z.leb_le in H;
    compute in H ; discriminate
  | H : 0 <= (Zneg _) |- _ =>
    rewrite <- Z.leb_le in H;
    compute in H ; discriminate
  end.

#[deprecated(since="9.0")]
Ltac lia p :=
  lia_step p ; lia_contr.

#[deprecated(since="9.0")]
Ltac slia H1 H2 :=
  normZ ; lia (Add (Hyp _ H1) (Hyp _ H2)).

Arguments Hyp {_} prf.
