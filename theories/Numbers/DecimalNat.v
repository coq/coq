(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * DecimalNat

    Proofs that conversions between decimal numbers and [nat]
    are bijections. *)

Require Import Decimal DecimalFacts Arith.

Module Unsigned.

(** A few helper functions used during proofs *)

Definition hd d :=
 match d with
 | Nil => 0
 | D0 _ => 0
 | D1 _ => 1
 | D2 _ => 2
 | D3 _ => 3
 | D4 _ => 4
 | D5 _ => 5
 | D6 _ => 6
 | D7 _ => 7
 | D8 _ => 8
 | D9 _ => 9
end.

Definition tl d :=
 match d with
 | Nil => d
 | D0 d | D1 d | D2 d | D3 d | D4 d | D5 d | D6 d | D7 d | D8 d | D9 d => d
end.

Fixpoint usize (d:uint) : nat :=
  match d with
  | Nil => 0
  | D0 d => S (usize d)
  | D1 d => S (usize d)
  | D2 d => S (usize d)
  | D3 d => S (usize d)
  | D4 d => S (usize d)
  | D5 d => S (usize d)
  | D6 d => S (usize d)
  | D7 d => S (usize d)
  | D8 d => S (usize d)
  | D9 d => S (usize d)
  end.

(** A direct version of [to_little_uint], not tail-recursive *)
Fixpoint to_lu n :=
 match n with
 | 0 => Decimal.zero
 | S n => Little.succ (to_lu n)
 end.

(** A direct version of [of_little_uint] *)
Fixpoint of_lu (d:uint) : nat :=
  match d with
  | Nil => 0
  | D0 d => 10 * of_lu d
  | D1 d => 1 + 10 * of_lu d
  | D2 d => 2 + 10 * of_lu d
  | D3 d => 3 + 10 * of_lu d
  | D4 d => 4 + 10 * of_lu d
  | D5 d => 5 + 10 * of_lu d
  | D6 d => 6 + 10 * of_lu d
  | D7 d => 7 + 10 * of_lu d
  | D8 d => 8 + 10 * of_lu d
  | D9 d => 9 + 10 * of_lu d
  end.

(** Properties of [to_lu] *)

Lemma to_lu_succ n : to_lu (S n) = Little.succ (to_lu n).
Proof.
 reflexivity.
Qed.

Lemma to_little_uint_succ n d :
 Nat.to_little_uint n (Little.succ d) =
  Little.succ (Nat.to_little_uint n d).
Proof.
 revert d; induction n; simpl; trivial.
Qed.

Lemma to_lu_equiv n :
  to_lu n = Nat.to_little_uint n zero.
Proof.
 induction n; simpl; trivial.
 now rewrite IHn, <- to_little_uint_succ.
Qed.

Lemma to_uint_alt n :
 Nat.to_uint n = rev (to_lu n).
Proof.
 unfold Nat.to_uint. f_equal. symmetry. apply to_lu_equiv.
Qed.

(** Properties of [of_lu] *)

Lemma of_lu_eqn d :
 of_lu d = hd d + 10 * of_lu (tl d).
Proof.
 induction d; simpl; trivial.
Qed.

Ltac simpl_of_lu :=
 match goal with
 | |- context [ of_lu (?f ?x) ] =>
   rewrite (of_lu_eqn (f x)); simpl hd; simpl tl
 end.

Lemma of_lu_succ d :
 of_lu (Little.succ d) = S (of_lu d).
Proof.
 induction d; trivial.
 simpl_of_lu. rewrite IHd. simpl_of_lu.
 now rewrite Nat.mul_succ_r, <- (Nat.add_comm 10).
Qed.

Lemma of_to_lu n :
 of_lu (to_lu n) = n.
Proof.
 induction n; simpl; trivial. rewrite of_lu_succ. now f_equal.
Qed.

Lemma of_lu_revapp d d' :
of_lu (revapp d d') =
 of_lu (rev d) + of_lu d' * 10^usize d.
Proof.
 revert d'.
 induction d; intro d'; simpl usize;
 [ simpl; now rewrite Nat.mul_1_r | .. ];
 unfold rev; simpl revapp; rewrite 2 IHd;
 rewrite <- Nat.add_assoc; f_equal; simpl_of_lu; simpl of_lu;
 rewrite Nat.pow_succ_r'; ring.
Qed.

Lemma of_uint_acc_spec n d :
 Nat.of_uint_acc d n = of_lu (rev d) + n * 10^usize d.
Proof.
 revert n. induction d; intros;
 simpl Nat.of_uint_acc; rewrite ?Nat.tail_mul_spec, ?IHd;
 simpl rev; simpl usize; rewrite ?Nat.pow_succ_r';
 [ simpl; now rewrite Nat.mul_1_r | .. ];
 unfold rev at 2; simpl revapp; rewrite of_lu_revapp;
 simpl of_lu; ring.
Qed.

Lemma of_uint_alt d : Nat.of_uint d = of_lu (rev d).
Proof.
 unfold Nat.of_uint. now rewrite of_uint_acc_spec.
Qed.

(** First main bijection result *)

Lemma of_to (n:nat) : Nat.of_uint (Nat.to_uint n) = n.
Proof.
 rewrite to_uint_alt, of_uint_alt, rev_rev. apply of_to_lu.
Qed.

(** The other direction *)

Lemma to_lu_tenfold n : n<>0 ->
 to_lu (10 * n) = D0 (to_lu n).
Proof.
 induction n.
 - simpl. now destruct 1.
 - intros _.
   destruct (Nat.eq_dec n 0) as [->|H]; simpl; trivial.
   rewrite !Nat.add_succ_r.
   simpl in *. rewrite (IHn H). now destruct (to_lu n).
Qed.

Lemma of_lu_0 d : of_lu d = 0 <-> nztail d = Nil.
Proof.
 induction d; try simpl_of_lu; try easy.
 rewrite Nat.add_0_l.
 split; intros H.
 - apply Nat.eq_mul_0_r in H; auto.
   rewrite IHd in H. simpl. now rewrite H.
 - simpl in H. destruct (nztail d); try discriminate.
   now destruct IHd as [_ ->].
Qed.

Lemma to_of_lu_tenfold d :
 to_lu (of_lu d) = lnorm d ->
 to_lu (10 * of_lu d) = lnorm (D0 d).
Proof.
 intro IH.
 destruct (Nat.eq_dec (of_lu d) 0) as [H|H].
 - rewrite H. simpl. rewrite of_lu_0 in H.
   unfold lnorm. simpl. now rewrite H.
 - rewrite (to_lu_tenfold _ H), IH.
   rewrite of_lu_0 in H.
   unfold lnorm. simpl. now destruct (nztail d).
Qed.

Lemma to_of_lu d : to_lu (of_lu d) = lnorm d.
Proof.
 induction d; [ reflexivity | .. ];
 simpl_of_lu;
 rewrite ?Nat.add_succ_l, Nat.add_0_l, ?to_lu_succ, to_of_lu_tenfold
  by assumption;
 unfold lnorm; simpl; now destruct nztail.
Qed.

(** Second bijection result *)

Lemma to_of (d:uint) : Nat.to_uint (Nat.of_uint d) = unorm d.
Proof.
 rewrite to_uint_alt, of_uint_alt, to_of_lu.
 apply rev_lnorm_rev.
Qed.

(** Some consequences *)

Lemma to_uint_inj n n' : Nat.to_uint n = Nat.to_uint n' -> n = n'.
Proof.
 intro EQ.
 now rewrite <- (of_to n), <- (of_to n'), EQ.
Qed.

Lemma to_uint_surj d : exists n, Nat.to_uint n = unorm d.
Proof.
 exists (Nat.of_uint d). apply to_of.
Qed.

Lemma of_uint_norm d : Nat.of_uint (unorm d) = Nat.of_uint d.
Proof.
 unfold Nat.of_uint. now induction d.
Qed.

Lemma of_inj d d' :
 Nat.of_uint d = Nat.of_uint d' -> unorm d = unorm d'.
Proof.
 intros. rewrite <- !to_of. now f_equal.
Qed.

Lemma of_iff d d' : Nat.of_uint d = Nat.of_uint d' <-> unorm d = unorm d'.
Proof.
 split. apply of_inj. intros E. rewrite <- of_uint_norm, E.
 apply of_uint_norm.
Qed.

End Unsigned.

(** Conversion from/to signed decimal numbers *)

Module Signed.

Lemma of_to (n:nat) : Nat.of_int (Nat.to_int n) = Some n.
Proof.
 unfold Nat.to_int, Nat.of_int, norm. f_equal.
 rewrite Unsigned.of_uint_norm. apply Unsigned.of_to.
Qed.

Lemma to_of (d:int)(n:nat) : Nat.of_int d = Some n -> Nat.to_int n = norm d.
Proof.
 unfold Nat.of_int.
 destruct (norm d) eqn:Hd; intros [= <-].
 unfold Nat.to_int. rewrite Unsigned.to_of. f_equal.
 revert Hd; destruct d; simpl.
 - intros [= <-]. apply unorm_invol.
 - destruct (nzhead d); now intros [= <-].
Qed.

Lemma to_int_inj n n' : Nat.to_int n = Nat.to_int n' -> n = n'.
Proof.
 intro E.
 assert (E' : Some n = Some n').
 { now rewrite <- (of_to n), <- (of_to n'), E. }
 now injection E'.
Qed.

Lemma to_int_pos_surj d : exists n, Nat.to_int n = norm (Pos d).
Proof.
 exists (Nat.of_uint d). unfold Nat.to_int. now rewrite Unsigned.to_of.
Qed.

Lemma of_int_norm d : Nat.of_int (norm d) = Nat.of_int d.
Proof.
 unfold Nat.of_int. now rewrite norm_invol.
Qed.

Lemma of_inj_pos d d' :
 Nat.of_int (Pos d) = Nat.of_int (Pos d') -> unorm d = unorm d'.
Proof.
 unfold Nat.of_int. simpl. intros [= H]. apply Unsigned.of_inj.
 now rewrite <- Unsigned.of_uint_norm, H, Unsigned.of_uint_norm.
Qed.

End Signed.
