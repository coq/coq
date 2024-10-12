(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * HexadecimalN

    Proofs that conversions between hexadecimal numbers and [N]
    are bijections *)

Require Import Hexadecimal HexadecimalFacts HexadecimalPos PArith NArith.

Module Unsigned.

Lemma of_to (n:N) : N.of_hex_uint (N.to_hex_uint n) = n.
Proof.
  destruct n.
  - reflexivity.
  - apply HexadecimalPos.Unsigned.of_to.
Qed.

Lemma to_of (d:uint) : N.to_hex_uint (N.of_hex_uint d) = unorm d.
Proof.
  exact (HexadecimalPos.Unsigned.to_of d).
Qed.

Lemma to_uint_inj n n' : N.to_hex_uint n = N.to_hex_uint n' -> n = n'.
Proof.
  intros E. now rewrite <- (of_to n), <- (of_to n'), E.
Qed.

Lemma to_uint_surj d : exists p, N.to_hex_uint p = unorm d.
Proof.
  exists (N.of_hex_uint d). apply to_of.
Qed.

Lemma of_uint_norm d : N.of_hex_uint (unorm d) = N.of_hex_uint d.
Proof.
  now induction d.
Qed.

Lemma of_inj d d' :
  N.of_hex_uint d = N.of_hex_uint d' -> unorm d = unorm d'.
Proof.
  intros. rewrite <- !to_of. now f_equal.
Qed.

Lemma of_iff d d' : N.of_hex_uint d = N.of_hex_uint d' <-> unorm d = unorm d'.
Proof.
  split.
  - apply of_inj.
  - intros E. rewrite <- of_uint_norm, E.
    apply of_uint_norm.
Qed.

End Unsigned.

(** Conversion from/to signed hexadecimal numbers *)

Module Signed.

Lemma of_to (n:N) : N.of_hex_int (N.to_hex_int n) = Some n.
Proof.
  unfold N.to_hex_int, N.of_hex_int, norm. f_equal.
  rewrite Unsigned.of_uint_norm. apply Unsigned.of_to.
Qed.

Lemma to_of (d:int)(n:N) : N.of_hex_int d = Some n -> N.to_hex_int n = norm d.
Proof.
  unfold N.of_hex_int.
  destruct (norm d) eqn:Hd; intros [= <-].
  unfold N.to_hex_int. rewrite Unsigned.to_of. f_equal.
  revert Hd; destruct d; simpl.
  - intros [= <-]. apply unorm_involutive.
  - destruct (nzhead d); now intros [= <-].
Qed.

Lemma to_int_inj n n' : N.to_hex_int n = N.to_hex_int n' -> n = n'.
Proof.
  intro E.
  assert (E' : Some n = Some n').
  { now rewrite <- (of_to n), <- (of_to n'), E. }
  now injection E'.
Qed.

Lemma to_int_pos_surj d : exists n, N.to_hex_int n = norm (Pos d).
Proof.
  exists (N.of_hex_uint d). unfold N.to_hex_int. now rewrite Unsigned.to_of.
Qed.

Lemma of_int_norm d : N.of_hex_int (norm d) = N.of_hex_int d.
Proof.
  unfold N.of_hex_int. now rewrite norm_involutive.
Qed.

Lemma of_inj_pos d d' :
  N.of_hex_int (Pos d) = N.of_hex_int (Pos d') -> unorm d = unorm d'.
Proof.
  unfold N.of_hex_int. simpl. intros [= H]. apply Unsigned.of_inj.
  change Pos.of_hex_uint with N.of_hex_uint in H.
  now rewrite <- Unsigned.of_uint_norm, H, Unsigned.of_uint_norm.
Qed.

End Signed.
