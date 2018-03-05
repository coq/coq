(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Bit vectors interpreted as integers.
    Contribution by Jean Duprat (ENS Lyon). *)

Require Import Bvector.
Require Import ZArith.
Require Export Zpower.
Require Import Omega.

(** The evaluation of boolean vector is done both in binary and
    two's complement. The computed number belongs to Z.
    We hence use Omega to perform computations in Z.
    Moreover, we use functions [2^n] where [n] is a natural number
    (here the vector length).
*)


Section VALUE_OF_BOOLEAN_VECTORS.

(** Computations are done in the usual convention.
    The values correspond either to the binary coding (nat) or
    to the two's complement coding (int).
    We perform the computation via Horner scheme.
    The two's complement coding only makes sense on vectors whose
    size is greater or equal to one (a sign bit should be present).
*)

  Definition bit_value (b:bool) : Z :=
    match b with
      | true => 1%Z
      | false => 0%Z
    end.

  Lemma binary_value : forall n:nat, Bvector n -> Z.
  Proof.
    refine (nat_rect _ _ _); intros.
    exact 0%Z.

    inversion H0.
    exact (bit_value h + 2 * H H2)%Z.
  Defined.

  Lemma two_compl_value : forall n:nat, Bvector (S n) -> Z.
  Proof.
    simple induction n; intros.
    inversion H.
    exact (- bit_value h)%Z.

    inversion H0.
    exact (bit_value h + 2 * H H2)%Z.
  Defined.

End VALUE_OF_BOOLEAN_VECTORS.

Section ENCODING_VALUE.

(** We compute the binary value via a Horner scheme.
    Computation stops at the vector length without checks.
    We define a function Zmod2 similar to Z.div2 returning the
    quotient of division z=2q+r with 0<=r<=1.
    The two's complement value is also computed via a Horner scheme
    with Zmod2, the parameter is the size minus one.
*)

  Definition Zmod2 (z:Z) :=
    match z with
      | Z0 => 0%Z
      | Zpos p => match p with
		    | xI q => Zpos q
		    | xO q => Zpos q
		    | xH => 0%Z
		  end
      | Zneg p =>
	match p with
	  | xI q => (Zneg q - 1)%Z
	  | xO q => Zneg q
	  | xH => (-1)%Z
	end
    end.


  Lemma Zmod2_twice :
    forall z:Z, z = (2 * Zmod2 z + bit_value (Z.odd z))%Z.
  Proof.
    destruct z; simpl.
    trivial.

    destruct p; simpl; trivial.

    destruct p; simpl.
    destruct p as [p| p| ]; simpl.
    rewrite <- (Pos.pred_double_succ p); trivial.

    trivial.

    trivial.

    trivial.

    trivial.
  Qed.

  Lemma Z_to_binary : forall n:nat, Z -> Bvector n.
  Proof.
    simple induction n; intros.
    exact Bnil.

    exact (Bcons (Z.odd H0) n0 (H (Z.div2 H0))).
  Defined.

  Lemma Z_to_two_compl : forall n:nat, Z -> Bvector (S n).
  Proof.
    simple induction n; intros.
    exact (Bcons (Z.odd H) 0 Bnil).

    exact (Bcons (Z.odd H0) (S n0) (H (Zmod2 H0))).
  Defined.

End ENCODING_VALUE.

Section Z_BRIC_A_BRAC.

  (** Some auxiliary lemmas used in the next section. Large use of ZArith.
      Deserve to be properly rewritten.
  *)

  Lemma binary_value_Sn :
    forall (n:nat) (b:bool) (bv:Bvector n),
      binary_value (S n) ( b :: bv) =
      (bit_value b + 2 * binary_value n bv)%Z.
  Proof.
    intros; auto.
  Qed.

  Lemma Z_to_binary_Sn :
    forall (n:nat) (b:bool) (z:Z),
      (z >= 0)%Z ->
      Z_to_binary (S n) (bit_value b + 2 * z) = Bcons b n (Z_to_binary n z).
  Proof.
    destruct b; destruct z; simpl; auto.
    intro H; elim H; trivial.
  Qed.

  Lemma binary_value_pos :
    forall (n:nat) (bv:Bvector n), (binary_value n bv >= 0)%Z.
  Proof.
    induction bv as [| a n v IHbv]; cbn.
    omega.

    destruct a; destruct (binary_value n v); simpl; auto.
    auto with zarith.
  Qed.

  Lemma two_compl_value_Sn :
    forall (n:nat) (bv:Bvector (S n)) (b:bool),
      two_compl_value (S n) (Bcons b (S n) bv) =
      (bit_value b + 2 * two_compl_value n bv)%Z.
  Proof.
    intros; auto.
  Qed.

  Lemma Z_to_two_compl_Sn :
    forall (n:nat) (b:bool) (z:Z),
      Z_to_two_compl (S n) (bit_value b + 2 * z) =
      Bcons b (S n) (Z_to_two_compl n z).
  Proof.
    destruct b; destruct z as [| p| p]; auto.
    destruct p as [p| p| ]; auto.
    destruct p as [p| p| ]; simpl; auto.
    intros; rewrite (Pos.succ_pred_double p); trivial.
  Qed.

  Lemma Z_to_binary_Sn_z :
    forall (n:nat) (z:Z),
      Z_to_binary (S n) z =
      Bcons (Z.odd z) n (Z_to_binary n (Z.div2 z)).
  Proof.
    intros; auto.
  Qed.

  Lemma Z_div2_value :
    forall z:Z,
      (z >= 0)%Z -> (bit_value (Z.odd z) + 2 * Z.div2 z)%Z = z.
  Proof.
    destruct z as [| p| p]; auto.
    destruct p; auto.
    intro H; elim H; trivial.
  Qed.

  Lemma Pdiv2 : forall z:Z, (z >= 0)%Z -> (Z.div2 z >= 0)%Z.
  Proof.
    destruct z as [| p| p].
    auto.

    destruct p; auto.
    simpl; intros; omega.

    intro H; elim H; trivial.
  Qed.

  Lemma Zdiv2_two_power_nat :
    forall (z:Z) (n:nat),
      (z >= 0)%Z ->
      (z < two_power_nat (S n))%Z -> (Z.div2 z < two_power_nat n)%Z.
  Proof.
    intros.
    enough (2 * Z.div2 z < 2 * two_power_nat n)%Z by omega.
    rewrite <- two_power_nat_S.
    destruct (Zeven.Zeven_odd_dec z) as [Heven|Hodd]; intros.
    rewrite <- Zeven.Zeven_div2; auto.
    generalize (Zeven.Zodd_div2 z Hodd); omega.
  Qed.

  Lemma Z_to_two_compl_Sn_z :
    forall (n:nat) (z:Z),
      Z_to_two_compl (S n) z =
      Bcons (Z.odd z) (S n) (Z_to_two_compl n (Zmod2 z)).
  Proof.
    intros; auto.
  Qed.

  Lemma Zeven_bit_value :
    forall z:Z, Zeven.Zeven z -> bit_value (Z.odd z) = 0%Z.
  Proof.
    destruct z; unfold bit_value; auto.
    destruct p; tauto || (intro H; elim H).
    destruct p; tauto || (intro H; elim H).
  Qed.

  Lemma Zodd_bit_value :
    forall z:Z, Zeven.Zodd z -> bit_value (Z.odd z) = 1%Z.
  Proof.
    destruct z; unfold bit_value; auto.
    intros; elim H.
    destruct p; tauto || (intros; elim H).
    destruct p; tauto || (intros; elim H).
  Qed.

  Lemma Zge_minus_two_power_nat_S :
    forall (n:nat) (z:Z),
      (z >= - two_power_nat (S n))%Z -> (Zmod2 z >= - two_power_nat n)%Z.
  Proof.
    intros n z; rewrite (two_power_nat_S n).
    generalize (Zmod2_twice z).
    destruct (Zeven.Zeven_odd_dec z) as [H| H].
    rewrite (Zeven_bit_value z H); intros; omega.

    rewrite (Zodd_bit_value z H); intros; omega.
  Qed.

  Lemma Zlt_two_power_nat_S :
    forall (n:nat) (z:Z),
      (z < two_power_nat (S n))%Z -> (Zmod2 z < two_power_nat n)%Z.
  Proof.
    intros n z; rewrite (two_power_nat_S n).
    generalize (Zmod2_twice z).
    destruct (Zeven.Zeven_odd_dec z) as [H| H].
    rewrite (Zeven_bit_value z H); intros; omega.

    rewrite (Zodd_bit_value z H); intros; omega.
  Qed.

End Z_BRIC_A_BRAC.

Section COHERENT_VALUE.

(** We check that the functions are reciprocal on the definition interval.
    This uses earlier library lemmas.
*)

  Lemma binary_to_Z_to_binary :
    forall (n:nat) (bv:Bvector n), Z_to_binary n (binary_value n bv) = bv.
  Proof.
    induction bv as [| a n bv IHbv].
    auto.

    rewrite binary_value_Sn.
    rewrite Z_to_binary_Sn.
    rewrite IHbv; trivial.

    apply binary_value_pos.
  Qed.

  Lemma two_compl_to_Z_to_two_compl :
    forall (n:nat) (bv:Bvector n) (b:bool),
      Z_to_two_compl n (two_compl_value n (Bcons b n bv)) = Bcons b n bv.
  Proof.
    induction bv as [| a n bv IHbv]; intro b.
    destruct b; auto.

    rewrite two_compl_value_Sn.
    rewrite Z_to_two_compl_Sn.
    rewrite IHbv; trivial.
  Qed.

  Lemma Z_to_binary_to_Z :
    forall (n:nat) (z:Z),
      (z >= 0)%Z ->
      (z < two_power_nat n)%Z -> binary_value n (Z_to_binary n z) = z.
  Proof.
    induction n as [| n IHn].
    unfold two_power_nat, shift_nat; simpl; intros; omega.

    intros; rewrite Z_to_binary_Sn_z.
    rewrite binary_value_Sn.
    rewrite IHn.
    apply Z_div2_value; auto.

    apply Pdiv2; trivial.

    apply Zdiv2_two_power_nat; trivial.
  Qed.

  Lemma Z_to_two_compl_to_Z :
    forall (n:nat) (z:Z),
      (z >= - two_power_nat n)%Z ->
      (z < two_power_nat n)%Z -> two_compl_value n (Z_to_two_compl n z) = z.
  Proof.
    induction n as [| n IHn].
    unfold two_power_nat, shift_nat; simpl; intros.
    assert (z = (-1)%Z \/ z = 0%Z). omega.
    intuition; subst z; trivial.

    intros; rewrite Z_to_two_compl_Sn_z.
    rewrite two_compl_value_Sn.
    rewrite IHn.
    generalize (Zmod2_twice z); omega.

    apply Zge_minus_two_power_nat_S; auto.

    apply Zlt_two_power_nat_S; auto.
  Qed.

End COHERENT_VALUE.
