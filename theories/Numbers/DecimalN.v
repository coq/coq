(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * DecimalN

    Proofs that conversions between decimal numbers and [N]
    are bijections *)

Require Import Decimal DecimalFacts DecimalPos PArith NArith.

Module Unsigned.

Lemma of_to (n:N) : N.of_uint (N.to_uint n) = n.
Proof.
 destruct n.
 - reflexivity.
 - apply DecimalPos.Unsigned.of_to.
Qed.

Lemma to_of (d:uint) : N.to_uint (N.of_uint d) = unorm d.
Proof.
 exact (DecimalPos.Unsigned.to_of d).
Qed.

Lemma to_uint_inj n n' : N.to_uint n = N.to_uint n' -> n = n'.
Proof.
 intros E. now rewrite <- (of_to n), <- (of_to n'), E.
Qed.

Lemma to_uint_surj d : exists p, N.to_uint p = unorm d.
Proof.
 exists (N.of_uint d). apply to_of.
Qed.

Lemma of_uint_norm d : N.of_uint (unorm d) = N.of_uint d.
Proof.
 now induction d.
Qed.

Lemma of_inj d d' :
 N.of_uint d = N.of_uint d' -> unorm d = unorm d'.
Proof.
 intros. rewrite <- !to_of. now f_equal.
Qed.

Lemma of_iff d d' : N.of_uint d = N.of_uint d' <-> unorm d = unorm d'.
Proof.
 split. apply of_inj. intros E. rewrite <- of_uint_norm, E.
 apply of_uint_norm.
Qed.

End Unsigned.

(** Conversion from/to signed decimal numbers *)

Module Signed.

Lemma of_to (n:N) : N.of_int (N.to_int n) = Some n.
Proof.
 unfold N.to_int, N.of_int, norm. f_equal.
 rewrite Unsigned.of_uint_norm. apply Unsigned.of_to.
Qed.

Lemma to_of (d:int)(n:N) : N.of_int d = Some n -> N.to_int n = norm d.
Proof.
 unfold N.of_int.
 destruct (norm d) eqn:Hd; intros [= <-].
 unfold N.to_int. rewrite Unsigned.to_of. f_equal.
 revert Hd; destruct d; simpl.
 - intros [= <-]. apply unorm_invol.
 - destruct (nzhead d); now intros [= <-].
Qed.

Lemma to_int_inj n n' : N.to_int n = N.to_int n' -> n = n'.
Proof.
 intro E.
 assert (E' : Some n = Some n').
 { now rewrite <- (of_to n), <- (of_to n'), E. }
 now injection E'.
Qed.

Lemma to_int_pos_surj d : exists n, N.to_int n = norm (Pos d).
Proof.
 exists (N.of_uint d). unfold N.to_int. now rewrite Unsigned.to_of.
Qed.

Lemma of_int_norm d : N.of_int (norm d) = N.of_int d.
Proof.
 unfold N.of_int. now rewrite norm_invol.
Qed.

Lemma of_inj_pos d d' :
 N.of_int (Pos d) = N.of_int (Pos d') -> unorm d = unorm d'.
Proof.
 unfold N.of_int. simpl. intros [= H]. apply Unsigned.of_inj.
 change Pos.of_uint with N.of_uint in H.
 now rewrite <- Unsigned.of_uint_norm, H, Unsigned.of_uint_norm.
Qed.

End Signed.
