(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * DecimalZ

    Proofs that conversions between decimal numbers and [Z]
    are bijections. *)

Require Import Decimal DecimalFacts DecimalPos DecimalN ZArith.

Lemma of_to (z:Z) : Z.of_int (Z.to_int z) = z.
Proof.
  destruct z; simpl.
  - trivial.
  - unfold Z.of_uint. rewrite DecimalPos.Unsigned.of_to. now destruct p.
  - unfold Z.of_uint. rewrite DecimalPos.Unsigned.of_to. destruct p; auto.
Qed.

Lemma to_of (d:int) : Z.to_int (Z.of_int d) = norm d.
Proof.
  destruct d; simpl; unfold Z.to_int, Z.of_uint.
  - rewrite <- (DecimalN.Unsigned.to_of d). unfold N.of_uint.
    now destruct (Pos.of_uint d).
  - destruct (Pos.of_uint d) eqn:Hd; simpl; f_equal.
    + generalize (DecimalPos.Unsigned.to_of d). rewrite Hd. simpl.
      intros H. symmetry in H. apply unorm_0 in H. now rewrite H.
    + assert (Hp := DecimalPos.Unsigned.to_of d). rewrite Hd in Hp. simpl in *.
      rewrite Hp. unfold unorm in *.
      destruct (nzhead d); trivial.
      generalize (DecimalPos.Unsigned.of_to p). now rewrite Hp.
Qed.

(** Some consequences *)

Lemma to_int_inj n n' : Z.to_int n = Z.to_int n' -> n = n'.
Proof.
  intro EQ.
  now rewrite <- (of_to n), <- (of_to n'), EQ.
Qed.

Lemma to_int_surj d : exists n, Z.to_int n = norm d.
Proof.
  exists (Z.of_int d). apply to_of.
Qed.

Lemma of_int_norm d : Z.of_int (norm d) = Z.of_int d.
Proof.
  unfold Z.of_int, Z.of_uint.
  destruct d.
  - simpl. now rewrite DecimalPos.Unsigned.of_uint_norm.
  - simpl. destruct (nzhead d) eqn:H;
    [ induction d; simpl; auto; discriminate |
      destruct (nzhead_nonzero _ _ H) | .. ];
    f_equal; f_equal; apply DecimalPos.Unsigned.of_iff;
    unfold unorm; now rewrite H.
Qed.

Lemma of_inj d d' :
  Z.of_int d = Z.of_int d' -> norm d = norm d'.
Proof.
  intros. rewrite <- !to_of. now f_equal.
Qed.

Lemma of_iff d d' : Z.of_int d = Z.of_int d' <-> norm d = norm d'.
Proof.
  split.
  - apply of_inj.
  - intros E. rewrite <- of_int_norm, E.
    apply of_int_norm.
Qed.

(** Various lemmas *)

Lemma of_uint_iter_D0 d n :
  Z.of_uint (app d (Nat.iter n D0 Nil)) = Nat.iter n (Z.mul 10) (Z.of_uint d).
Proof.
  rewrite <-(rev_rev (app _ _)), <-(of_list_to_list (rev (app _ _))).
  rewrite rev_spec, app_spec, List.rev_app_distr.
  rewrite <-!rev_spec, <-app_spec, of_list_to_list.
  unfold Z.of_uint; rewrite Unsigned.of_lu_rev.
  unfold app; rewrite Unsigned.of_lu_revapp, !rev_rev.
  rewrite <-!Unsigned.of_lu_rev, !rev_rev.
  assert (H' : Pos.of_uint (Nat.iter n D0 Nil) = 0%N).
  { now induction n; [|rewrite Unsigned.nat_iter_S]. }
  rewrite H', N.add_0_l; clear H'.
  induction n; [now simpl; rewrite N.mul_1_r|].
  rewrite !Unsigned.nat_iter_S, <-IHn.
  simpl Unsigned.usize; rewrite N.pow_succ_r'.
  rewrite !N2Z.inj_mul; simpl Z.of_N; ring.
Qed.

Lemma of_int_iter_D0 d n :
  Z.of_int (app_int d (Nat.iter n D0 Nil)) = Nat.iter n (Z.mul 10) (Z.of_int d).
Proof.
  case d; clear d; intro d; simpl.
  - now rewrite of_uint_iter_D0.
  - rewrite of_uint_iter_D0; induction n; [now simpl|].
    rewrite !Unsigned.nat_iter_S, <-IHn; ring.
Qed.

Lemma nztail_to_uint_pow10 n :
  Decimal.nztail (Pos.to_uint (Nat.iter n (Pos.mul 10) 1%positive))
  = (D1 Nil, n).
Proof.
  case n as [|n]; [now simpl|].
  rewrite <-(Nat2Pos.id (S n)); [|now simpl].
  generalize (Pos.of_nat (S n)); clear n; intro p.
  induction (Pos.to_nat p); [now simpl|].
  rewrite Unsigned.nat_iter_S.
  unfold Pos.to_uint.
  change (Pos.to_little_uint _)
    with (Unsigned.to_lu (10 * N.pos (Nat.iter n (Pos.mul 10) 1%positive))).
  rewrite Unsigned.to_ldec_tenfold.
  revert IHn; unfold Pos.to_uint.
  unfold Decimal.nztail; rewrite !rev_rev; simpl.
  set (f'' := _ (Pos.to_little_uint _)).
  now case f''; intros r n' H; inversion H.
Qed.
