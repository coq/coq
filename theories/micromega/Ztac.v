(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Tactics for doing arithmetic proofs.
    Useful to bootstrap lia.
 *)

Require Import ZArithRing.
Require Import ZArith_base.
Local Open Scope Z_scope.

Lemma eq_incl :
  forall (x y:Z), x = y -> x <= y /\ y <= x.
Proof.
  intros; split;
  apply Z.eq_le_incl; auto.
Qed.

Lemma elim_concl_eq :
  forall x y, (x < y \/ y < x -> False) -> x = y.
Proof.
  intros x y H.
  destruct (Z_lt_le_dec x y).
  exfalso. apply H ; auto.
  destruct (Zle_lt_or_eq y x);auto.
  exfalso.
  apply H ; auto.
Qed.

Lemma elim_concl_le :
  forall x y, (y < x -> False) -> x <= y.
Proof.
  intros x y H.
  destruct (Z_lt_le_dec y x).
  exfalso ; auto.
  auto.
Qed.

Lemma elim_concl_lt :
  forall x y, (y <= x -> False) -> x < y.
Proof.
  intros x y H.
  destruct (Z_lt_le_dec x y).
  auto.
  exfalso ; auto.
Qed.



Lemma Zlt_le_add_1 : forall n m : Z, n < m -> n + 1 <= m.
Proof. exact (Zlt_le_succ). Qed.


Ltac normZ :=
  repeat
  match goal with
  | H : _ < _ |- _ =>  apply Zlt_le_add_1 in H
  | H : ?Y <= _ |- _ =>
    lazymatch Y with
    | 0 => fail
    | _ => apply Zle_minus_le_0 in H
    end
  | H : _ >= _ |- _ => apply Z.ge_le in H
  | H : _ > _  |- _ => apply Z.gt_lt in H
  | H : _ = _  |- _ => apply eq_incl in H ; destruct H
  | |- @eq Z _ _  => apply elim_concl_eq ; let H := fresh "HZ" in intros [H|H]
  | |- _ <= _ => apply elim_concl_le ; intros
  | |- _ < _ => apply elim_concl_lt ; intros
  | |- _ >= _ => apply Z.le_ge
  end.


Inductive proof :=
| Hyp (e : Z) (prf : 0 <= e)
| Add (p1 p2: proof)
| Mul (p1 p2: proof)
| Cst (c : Z)
.

Lemma add_le : forall e1 e2, 0 <= e1 -> 0 <= e2 -> 0 <= e1+e2.
Proof.
  intros.
  change 0 with (0+ 0).
  apply Z.add_le_mono; auto.
Qed.

Lemma mul_le : forall e1 e2, 0 <= e1 -> 0 <= e2 -> 0 <= e1*e2.
Proof.
  intros e1 e2 H H0.
  change 0 with (0* e2).
  apply Zmult_le_compat_r; auto.
Qed.

Fixpoint eval_proof (p : proof) : { e : Z | 0 <= e} :=
  match p with
  | Hyp e prf => exist _ e prf
  | Add p1 p2 => let (e1,p1) := eval_proof p1 in
                 let (e2,p2) := eval_proof p2 in
                 exist _ _ (add_le _ _ p1 p2)
  | Mul p1 p2  => let (e1,p1) := eval_proof p1 in
                 let (e2,p2) := eval_proof p2 in
                 exist _ _ (mul_le _ _ p1 p2)
  | Cst c      =>  match Z_le_dec 0 c with
                   | left prf => exist _ _ prf
                   |  _       => exist _ _ Z.le_0_1
                 end
  end.

Ltac lia_step p :=
  let H := fresh in
  let prf := (eval cbn - [Z.le Z.mul Z.opp Z.sub Z.add] in (eval_proof p)) in
  match prf with
  | @exist _ _ _ ?P =>  pose proof P as H
  end ; ring_simplify in H.

Ltac lia_contr :=
  match goal with
  | H : 0 <= - (Zpos _) |- _ =>
    rewrite <- Z.leb_le in H;
    compute in H ; discriminate
  | H : 0 <= (Zneg _) |- _ =>
    rewrite <- Z.leb_le in H;
    compute in H ; discriminate
  end.


Ltac lia p :=
  lia_step p ; lia_contr.

Ltac slia H1 H2 :=
  normZ ; lia (Add (Hyp _ H1) (Hyp _ H2)).

Arguments Hyp {_} prf.
