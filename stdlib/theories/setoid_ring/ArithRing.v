(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PeanoNat.
Require Import BinNat.
Require Import Nnat.
Require Export Ring.
Set Implicit Arguments.

Lemma natSRth : semi_ring_theory O (S O) plus mult (@eq nat).
 Proof.
   constructor.
   - exact Nat.add_0_l.
   - exact Nat.add_comm.
   - exact Nat.add_assoc.
   - exact Nat.mul_1_l.
   - exact Nat.mul_0_l.
   - exact Nat.mul_comm.
   - exact Nat.mul_assoc.
   - exact Nat.mul_add_distr_r.
 Qed.

Lemma nat_morph_N :
   semi_morph 0 1 plus mult (eq (A:=nat))
          0%N 1%N N.add N.mul N.eqb N.to_nat.
Proof.
  constructor;trivial.
  - exact N2Nat.inj_add.
  - exact N2Nat.inj_mul.
  - intros x y H. apply N.eqb_eq in H. now subst.
Qed.

Ltac natcst t :=
  match isnatcst t with
    true => constr:(N.of_nat t)
  | _ => constr:(InitialRing.NotConstant)
  end.

Ltac Ss_to_add f acc :=
  match f with
  | S ?f1 => Ss_to_add f1 (S acc)
  | _ => constr:((acc + f)%nat)
  end.

(* For internal use only *)
Local Definition protected_to_nat := N.to_nat.

Ltac natprering :=
  match goal with
  |- context C [S ?p] =>
    match p with
      O => fail 1 (* avoid replacing 1 with 1+0 ! *)
    | p => match isnatcst p with
           | true => fail 1
           | false => let v := Ss_to_add p (S 0) in
                         fold v; natprering
           end
    end
  | _ => change N.to_nat with protected_to_nat
  end.

Ltac natpostring :=
  match goal with
  | |- context [N.to_nat ?x] =>
    let v := eval cbv in (N.to_nat x) in
    change (N.to_nat x) with v;
    natpostring
  | _ => change protected_to_nat with N.to_nat
  end.

Add Ring natr : natSRth
  (morphism nat_morph_N, constants [natcst],
   preprocess [natprering], postprocess [natpostring]).
