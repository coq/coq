(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This library has been deprecated since Coq version 8.10. *)

(** * Int31 numbers defines Z/(2^31)Z, and can hence be equipped
      with a ring structure and a ring tactic *)

Require Import Int31 Cyclic31 CyclicAxioms.

Local Open Scope int31_scope.

(** Detection of constants *)

Local Open Scope list_scope.

Ltac isInt31cst_lst l :=
 match l with
 | nil => constr:(true)
 | ?t::?l => match t with
               | D1 => isInt31cst_lst l
               | D0 => isInt31cst_lst l
               | _ => constr:(false)
             end
 | _ => constr:(false)
 end.

Ltac isInt31cst t :=
 match t with
 | I31 ?i0 ?i1 ?i2 ?i3 ?i4 ?i5 ?i6 ?i7 ?i8 ?i9 ?i10
       ?i11 ?i12 ?i13 ?i14 ?i15 ?i16 ?i17 ?i18 ?i19 ?i20
       ?i21 ?i22 ?i23 ?i24 ?i25 ?i26 ?i27 ?i28 ?i29 ?i30 =>
    let l :=
      constr:(i0::i1::i2::i3::i4::i5::i6::i7::i8::i9::i10
      ::i11::i12::i13::i14::i15::i16::i17::i18::i19::i20
      ::i21::i22::i23::i24::i25::i26::i27::i28::i29::i30::nil)
    in isInt31cst_lst l
 | Int31.On => constr:(true)
 | Int31.In => constr:(true)
 | Int31.Tn => constr:(true)
 | Int31.Twon => constr:(true)
 | _ => constr:(false)
 end.

Ltac Int31cst t :=
 match isInt31cst t with
 | true => constr:(t)
 | false => constr:(NotConstant)
 end.

(** The generic ring structure inferred from the Cyclic structure *)

Module Int31ring := CyclicRing Int31Cyclic.

(** Unlike in the generic [CyclicRing], we can use Leibniz here. *)

Lemma Int31_canonic : forall x y, phi x = phi y -> x = y.
Proof.
 intros x y EQ.
 now rewrite <- (phi_inv_phi x), <- (phi_inv_phi y), EQ.
Qed.

Lemma ring_theory_switch_eq :
 forall A (R R':A->A->Prop) zero one add mul sub opp,
  (forall x y : A, R x y -> R' x y) ->
  ring_theory zero one add mul sub opp R ->
  ring_theory zero one add mul sub opp R'.
Proof.
intros A R R' zero one add mul sub opp Impl Ring.
constructor; intros; apply Impl; apply Ring.
Qed.

Lemma Int31Ring : ring_theory 0 1 add31 mul31 sub31 opp31 Logic.eq.
Proof.
exact (ring_theory_switch_eq _ _ _ _ _ _ _ _ _ Int31_canonic Int31ring.CyclicRing).
Qed.

Lemma eqb31_eq : forall x y, eqb31 x y = true <-> x=y.
Proof.
unfold eqb31. intros x y.
rewrite Cyclic31.spec_compare. case Z.compare_spec.
intuition. apply Int31_canonic; auto.
intuition; subst; auto with zarith; try discriminate.
intuition; subst; auto with zarith; try discriminate.
Qed.

Lemma eqb31_correct : forall x y, eqb31 x y = true -> x=y.
Proof. now apply eqb31_eq. Qed.

Add Ring Int31Ring : Int31Ring
 (decidable eqb31_correct,
  constants [Int31cst]).

Section TestRing.
Let test : forall x y, 1 + x*y + x*x + 1 = 1*1 + 1 + y*x + 1*x*x.
intros. ring.
Qed.
End TestRing.
