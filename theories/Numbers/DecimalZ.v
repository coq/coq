(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
 split. apply of_inj. intros E. rewrite <- of_int_norm, E.
 apply of_int_norm.
Qed.
