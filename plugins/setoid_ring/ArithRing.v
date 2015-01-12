(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Mult.
Require Import BinNat.
Require Import Nnat.
Require Export Ring.
Set Implicit Arguments.

Lemma natSRth : semi_ring_theory O (S O) plus mult (@eq nat).
 Proof.
  constructor. exact plus_0_l. exact plus_comm. exact plus_assoc.
  exact mult_1_l. exact mult_0_l. exact mult_comm. exact mult_assoc.
  exact mult_plus_distr_r.
 Qed.

Lemma nat_morph_N :
   semi_morph 0 1 plus mult (eq (A:=nat))
          0%N 1%N N.add N.mul N.eqb N.to_nat.
Proof.
  constructor;trivial.
  exact N2Nat.inj_add.
  exact N2Nat.inj_mul.
  intros x y H. apply N.eqb_eq in H. now subst.
Qed.

Ltac natcst t :=
  match isnatcst t with
    true => constr:(N.of_nat t)
  | _ => constr:InitialRing.NotConstant
  end.

Ltac Ss_to_add f acc :=
  match f with
  | S ?f1 => Ss_to_add f1 (S acc)
  | _ => constr:(acc + f)%nat
  end.

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
  | _ => idtac
  end.

Add Ring natr : natSRth
  (morphism nat_morph_N, constants [natcst], preprocess [natprering]).

