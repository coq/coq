(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Wf_nat ZArith_base Omega Zcomplements.
Require Export Zpow_def.
Local Open Scope Z_scope.

(** * Power functions over [Z] *)

(** Nota : this file is mostly deprecated. The definition of [Z.pow]
    and its usual properties are now provided by module [BinInt.Z].
    Powers of 2 are also available there (see [Z.shiftl] and [Z.shiftr]).
    Only remain here:
     - [Zpower_nat] : a power function with a [nat] exponent
     - old-style powers of two, such as [two_p]
     - [Zdiv_rest] : a division + modulo when the divisor is a power of 2
*)


(** [Zpower_nat z n] is the n-th power of [z] when [n] is an unary
    integer (type [nat]) and [z] a signed integer (type [Z]) *)

Definition Zpower_nat (z:Z) := nat_rect _ 1 (fun _ => Z.mul z).

Lemma Zpower_nat_0_r z : Zpower_nat z 0 = 1.
Proof. reflexivity. Qed.

Lemma Zpower_nat_succ_r n z : Zpower_nat z (S n) = z * (Zpower_nat z n).
Proof. reflexivity. Qed.

(** [Zpower_nat_is_exp] says [Zpower_nat] is a morphism for
    [plus : nat->nat->nat] and [Z.mul : Z->Z->Z] *)

Lemma Zpower_nat_is_exp :
  forall (n m:nat) (z:Z),
    Zpower_nat z (n + m) = Zpower_nat z n * Zpower_nat z m.
Proof.
 induction n.
 - intros. now rewrite Zpower_nat_0_r, Z.mul_1_l.
 - intros. simpl. now rewrite IHn, Z.mul_assoc.
Qed.

(** Conversions between powers of unary and binary integers *)

Lemma Zpower_pos_nat (z : Z) (p : positive) :
  Z.pow_pos z p = Zpower_nat z (Pos.to_nat p).
Proof.
  apply Pos2Nat.inj_iter.
Qed.

Lemma Zpower_nat_Z (z : Z) (n : nat) :
  Zpower_nat z n = z ^ (Z.of_nat n).
Proof.
 induction n. trivial.
 rewrite Zpower_nat_succ_r, Nat2Z.inj_succ, Z.pow_succ_r.
 now f_equal.
 apply Nat2Z.is_nonneg.
Qed.

Theorem Zpower_nat_Zpower z n : 0 <= n ->
 z^n = Zpower_nat z (Z.abs_nat n).
Proof.
 intros. now rewrite Zpower_nat_Z, Zabs2Nat.id_abs, Z.abs_eq.
Qed.

(** The function [(Z.pow_pos z)] is a morphism
   for [Pos.add : positive->positive->positive] and [Z.mul : Z->Z->Z] *)

Lemma Zpower_pos_is_exp (n m : positive)(z:Z) :
  Z.pow_pos z (n + m) = Z.pow_pos z n * Z.pow_pos z m.
Proof.
 now apply (Z.pow_add_r z (Zpos n) (Zpos m)).
Qed.

Hint Immediate Zpower_nat_is_exp Zpower_pos_is_exp : zarith.
Hint Unfold Z.pow_pos Zpower_nat: zarith.

Theorem Zpower_exp x n m :
  n >= 0 -> m >= 0 -> x ^ (n + m) = x ^ n * x ^ m.
Proof.
 Z.swap_greater. apply Z.pow_add_r.
Qed.

Section Powers_of_2.

  (** * Powers of 2 *)

  (** For the powers of two, that will be widely used, a more direct
      calculus is possible. [shift n m] computes [2^n * m], i.e.
      [m] shifted by [n] positions *)

  Definition shift_nat (n:nat) (z:positive) := nat_rect _ z (fun _ => xO) n.
  Definition shift_pos (n z:positive) := Pos.iter xO z n.
  Definition shift (n:Z) (z:positive) :=
    match n with
      | Z0 => z
      | Zpos p => Pos.iter xO z p
      | Zneg p => z
    end.

  Definition two_power_nat (n:nat) := Zpos (shift_nat n 1).
  Definition two_power_pos (x:positive) := Zpos (shift_pos x 1).

  Definition two_p (x:Z) :=
    match x with
      | Z0 => 1
      | Zpos y => two_power_pos y
      | Zneg y => 0
    end.

  (** Equivalence with notions defined in BinInt *)

  Lemma shift_nat_equiv n p : shift_nat n p = Pos.shiftl_nat p n.
  Proof. reflexivity. Qed.

  Lemma shift_pos_equiv n p : shift_pos n p = Pos.shiftl p (Npos n).
  Proof. reflexivity. Qed.

  Lemma shift_equiv n p : 0<=n -> Zpos (shift n p) = Z.shiftl (Zpos p) n.
  Proof.
   destruct n.
   - trivial.
   - simpl; intros. now apply Pos.iter_swap_gen.
   - now destruct 1.
  Qed.

  Lemma two_power_nat_equiv n : two_power_nat n = 2 ^ (Z.of_nat n).
  Proof.
   induction n.
   - trivial.
   - now rewrite Nat2Z.inj_succ, Z.pow_succ_r, <- IHn by apply Nat2Z.is_nonneg.
  Qed.

  Lemma two_power_pos_equiv p : two_power_pos p = 2 ^ Zpos p.
  Proof.
   now apply Pos.iter_swap_gen.
  Qed.

  Lemma two_p_equiv x : two_p x = 2 ^ x.
  Proof.
   destruct x; trivial. apply two_power_pos_equiv.
  Qed.

  (** Properties of these old versions of powers of two *)

  Lemma two_power_nat_S n : two_power_nat (S n) = 2 * two_power_nat n.
  Proof. reflexivity. Qed.

  Lemma shift_nat_plus n m x :
    shift_nat (n + m) x = shift_nat n (shift_nat m x).
  Proof.
   induction n; simpl; now f_equal.
  Qed.

  Theorem shift_nat_correct n x :
    Zpos (shift_nat n x) = Zpower_nat 2 n * Zpos x.
  Proof.
   induction n.
   - trivial.
   - now rewrite Zpower_nat_succ_r, <- Z.mul_assoc, <- IHn.
  Qed.

  Theorem two_power_nat_correct n : two_power_nat n = Zpower_nat 2 n.
  Proof.
   now rewrite two_power_nat_equiv, Zpower_nat_Z.
  Qed.

  Lemma shift_pos_nat p x : shift_pos p x = shift_nat (Pos.to_nat p) x.
  Proof.
   apply Pos2Nat.inj_iter.
  Qed.

  Lemma two_power_pos_nat p : two_power_pos p = two_power_nat (Pos.to_nat p).
  Proof.
   unfold two_power_pos. now rewrite shift_pos_nat.
  Qed.

  Theorem shift_pos_correct p x :
    Zpos (shift_pos p x) = Z.pow_pos 2 p * Zpos x.
  Proof.
   now rewrite shift_pos_nat, Zpower_pos_nat, shift_nat_correct.
  Qed.

  Theorem two_power_pos_correct x : two_power_pos x = Z.pow_pos 2 x.
  Proof.
   apply two_power_pos_equiv.
  Qed.

  Theorem two_power_pos_is_exp x y :
   two_power_pos (x + y) = two_power_pos x * two_power_pos y.
  Proof.
    rewrite 3 two_power_pos_equiv. now apply (Z.pow_add_r 2 (Zpos x) (Zpos y)).
  Qed.

  Lemma two_p_correct x : two_p x = 2^x.
  Proof (two_p_equiv x).

  Theorem two_p_is_exp x y :
    0 <= x -> 0 <= y -> two_p (x + y) = two_p x * two_p y.
  Proof.
    rewrite !two_p_equiv. apply Z.pow_add_r.
  Qed.

  Lemma two_p_gt_ZERO x : 0 <= x -> two_p x > 0.
  Proof.
   Z.swap_greater. rewrite two_p_equiv. now apply Z.pow_pos_nonneg.
  Qed.

  Lemma two_p_S x : 0 <= x -> two_p (Z.succ x) = 2 * two_p x.
  Proof.
   rewrite !two_p_equiv. now apply Z.pow_succ_r.
  Qed.

  Lemma two_p_pred x : 0 <= x -> two_p (Z.pred x) < two_p x.
  Proof.
   rewrite !two_p_equiv. intros. apply Z.pow_lt_mono_r; auto with zarith.
  Qed.

End Powers_of_2.

Hint Resolve two_p_gt_ZERO: zarith.
Hint Immediate two_p_pred two_p_S: zarith.

Section power_div_with_rest.

  (** * Division by a power of two. *)

  (** To [x:Z] and [p:positive], [q],[r] are associated such that
      [x = 2^p.q + r] and [0 <= r < 2^p] *)

  (** Invariant: [d*q + r = d'*q + r /\ d' = 2*d /\ 0<=r<d /\ 0<=r'<d'] *)
  Definition Zdiv_rest_aux (qrd:Z * Z * Z) :=
    let '(q,r,d) := qrd in
      (match q with
	 | Z0 => (0, r)
	 | Zpos xH => (0, d + r)
	 | Zpos (xI n) => (Zpos n, d + r)
	 | Zpos (xO n) => (Zpos n, r)
	 | Zneg xH => (-1, d + r)
	 | Zneg (xI n) => (Zneg n - 1, d + r)
	 | Zneg (xO n) => (Zneg n, r)
       end, 2 * d).

  Definition Zdiv_rest (x:Z) (p:positive) :=
    let (qr, d) := Pos.iter Zdiv_rest_aux (x, 0, 1) p in qr.

  Lemma Zdiv_rest_correct1 (x:Z) (p:positive) :
    let (_, d) := Pos.iter Zdiv_rest_aux (x, 0, 1) p in
    d = two_power_pos p.
  Proof.
   rewrite Pos2Nat.inj_iter, two_power_pos_nat.
   induction (Pos.to_nat p); simpl; trivial.
   destruct (nat_rect _ _ _ _) as ((q,r),d).
   unfold Zdiv_rest_aux. rewrite two_power_nat_S; now f_equal.
  Qed.

  Lemma Zdiv_rest_correct2 (x:Z) (p:positive) :
    let '(q,r,d) := Pos.iter Zdiv_rest_aux (x, 0, 1) p in
    x = q * d + r /\ 0 <= r < d.
  Proof.
   apply Pos.iter_invariant; [|omega].
   intros ((q,r),d) (H,H'). unfold Zdiv_rest_aux.
   destruct q as [ |[q|q| ]|[q|q| ]]; try omega.
   - rewrite Pos2Z.inj_xI, Z.mul_add_distr_r in H.
     rewrite Z.mul_shuffle3, Z.mul_assoc. omega.
   - rewrite Pos2Z.inj_xO in H.
     rewrite Z.mul_shuffle3, Z.mul_assoc. omega.
   - rewrite Pos2Z.neg_xI, Z.mul_sub_distr_r in H.
     rewrite Z.mul_sub_distr_r, Z.mul_shuffle3, Z.mul_assoc. omega.
   - rewrite Pos2Z.neg_xO in H.
     rewrite Z.mul_shuffle3, Z.mul_assoc. omega.
  Qed.

  (** Old-style rich specification by proof of existence *)

  Inductive Zdiv_rest_proofs (x:Z) (p:positive) : Set :=
    Zdiv_rest_proof :
    forall q r:Z,
      x = q * two_power_pos p + r ->
      0 <= r -> r < two_power_pos p -> Zdiv_rest_proofs x p.

  Lemma Zdiv_rest_correct (x:Z) (p:positive) : Zdiv_rest_proofs x p.
  Proof.
    generalize (Zdiv_rest_correct1 x p); generalize (Zdiv_rest_correct2 x p).
    destruct (Pos.iter Zdiv_rest_aux (x, 0, 1) p) as ((q,r),d).
    intros (H1,(H2,H3)) ->. now exists q r.
  Qed.

  (** Direct correctness of [Zdiv_rest] *)

  Lemma Zdiv_rest_ok x p :
    let (q,r) := Zdiv_rest x p in
    x = q * 2^(Zpos p) + r /\ 0 <= r < 2^(Zpos p).
  Proof.
   unfold Zdiv_rest.
   generalize (Zdiv_rest_correct1 x p); generalize (Zdiv_rest_correct2 x p).
   destruct (Pos.iter Zdiv_rest_aux (x, 0, 1) p) as ((q,r),d).
   intros H ->. now rewrite two_power_pos_equiv in H.
  Qed.

  (** Equivalence with [Z.shiftr] *)

  Lemma Zdiv_rest_shiftr x p :
   fst (Zdiv_rest x p) = Z.shiftr x (Zpos p).
  Proof.
   generalize (Zdiv_rest_ok x p). destruct (Zdiv_rest x p) as (q,r).
   intros (H,H'). simpl.
   rewrite Z.shiftr_div_pow2 by easy.
   apply Z.div_unique_pos with r; trivial. now rewrite Z.mul_comm.
  Qed.

End power_div_with_rest.
