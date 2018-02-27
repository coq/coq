(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * DecimalPos

    Proofs that conversions between decimal numbers and [positive]
    are bijections. *)

Require Import Decimal DecimalFacts PArith NArith.

Module Unsigned.

Local Open Scope N.

(** A direct version of [of_little_uint] *)
Fixpoint of_lu (d:uint) : N :=
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

Lemma of_lu_eqn d :
 of_lu d = hd d + 10 * (of_lu (tl d)).
Proof.
 induction d; simpl; trivial.
Qed.

Ltac simpl_of_lu :=
 match goal with
 | |- context [ of_lu (?f ?x) ] =>
   rewrite (of_lu_eqn (f x)); simpl hd; simpl tl
 end.

Fixpoint usize (d:uint) : N :=
  match d with
  | Nil => 0
  | D0 d => N.succ (usize d)
  | D1 d => N.succ (usize d)
  | D2 d => N.succ (usize d)
  | D3 d => N.succ (usize d)
  | D4 d => N.succ (usize d)
  | D5 d => N.succ (usize d)
  | D6 d => N.succ (usize d)
  | D7 d => N.succ (usize d)
  | D8 d => N.succ (usize d)
  | D9 d => N.succ (usize d)
  end.

Lemma of_lu_revapp d d' :
 of_lu (revapp d d') =
  of_lu (rev d) + of_lu d' * 10^usize d.
Proof.
 revert d'.
 induction d; simpl; intro d'; [ now rewrite N.mul_1_r | .. ];
 unfold rev; simpl revapp; rewrite 2 IHd;
 rewrite <- N.add_assoc; f_equal; simpl_of_lu; simpl of_lu;
 rewrite N.pow_succ_r'; ring.
Qed.

Definition Nadd n p :=
 match n with
 | N0 => p
 | Npos p0 => (p0+p)%positive
 end.

Lemma Nadd_simpl n p q : Npos (Nadd n (p * q)) = n + Npos p * Npos q.
Proof.
 now destruct n.
Qed.

Lemma of_uint_acc_eqn d acc : d<>Nil ->
 Pos.of_uint_acc d acc = Pos.of_uint_acc (tl d) (Nadd (hd d) (10*acc)).
Proof.
 destruct d; simpl; trivial. now destruct 1.
Qed.

Lemma of_uint_acc_rev d acc :
 Npos (Pos.of_uint_acc d acc) =
  of_lu (rev d) + (Npos acc) * 10^usize d.
Proof.
 revert acc.
 induction d; intros; simpl usize;
 [ simpl; now rewrite Pos.mul_1_r | .. ];
 rewrite N.pow_succ_r';
 unfold rev; simpl revapp; try rewrite of_lu_revapp; simpl of_lu;
 rewrite of_uint_acc_eqn by easy; simpl tl; simpl hd;
 rewrite IHd, Nadd_simpl; ring.
Qed.

Lemma of_uint_alt d : Pos.of_uint d = of_lu (rev d).
Proof.
 induction d; simpl; trivial; unfold rev; simpl revapp;
 rewrite of_lu_revapp; simpl of_lu; try apply of_uint_acc_rev.
 rewrite IHd. ring.
Qed.

Lemma of_lu_rev d : Pos.of_uint (rev d) = of_lu d.
Proof.
 rewrite of_uint_alt. now rewrite rev_rev.
Qed.

Lemma of_lu_double_gen d :
  of_lu (Little.double d) = N.double (of_lu d) /\
  of_lu (Little.succ_double d) = N.succ_double (of_lu d).
Proof.
 rewrite N.double_spec, N.succ_double_spec.
 induction d; try destruct IHd as (IH1,IH2);
 simpl Little.double; simpl Little.succ_double;
 repeat (simpl_of_lu; rewrite ?IH1, ?IH2); split; reflexivity || ring.
Qed.

Lemma of_lu_double d :
  of_lu (Little.double d) = N.double (of_lu d).
Proof.
 apply of_lu_double_gen.
Qed.

Lemma of_lu_succ_double d :
  of_lu (Little.succ_double d) = N.succ_double (of_lu d).
Proof.
 apply of_lu_double_gen.
Qed.

(** First bijection result *)

Lemma of_to (p:positive) : Pos.of_uint (Pos.to_uint p) = Npos p.
Proof.
 unfold Pos.to_uint.
 rewrite of_lu_rev.
 induction p; simpl; trivial.
 - now rewrite of_lu_succ_double, IHp.
 - now rewrite of_lu_double, IHp.
Qed.

(** The other direction *)

Definition to_lu n :=
  match n with
  | N0 => Decimal.zero
  | Npos p => Pos.to_little_uint p
  end.

Lemma succ_double_alt d :
  Little.succ_double d = Little.succ (Little.double d).
Proof.
 now induction d.
Qed.

Lemma double_succ d :
  Little.double (Little.succ d) =
  Little.succ (Little.succ_double d).
Proof.
 induction d; simpl; f_equal; auto using succ_double_alt.
Qed.

Lemma to_lu_succ n :
 to_lu (N.succ n) = Little.succ (to_lu n).
Proof.
 destruct n; simpl; trivial.
 induction p; simpl; rewrite ?IHp;
  auto using succ_double_alt, double_succ.
Qed.

Lemma nat_iter_S n {A} (f:A->A) i :
 Nat.iter (S n) f i = f (Nat.iter n f i).
Proof.
 reflexivity.
Qed.

Lemma nat_iter_0 {A} (f:A->A) i : Nat.iter 0 f i = i.
Proof.
 reflexivity.
Qed.

Lemma to_ldec_tenfold p :
 to_lu (10 * Npos p) = D0 (to_lu (Npos p)).
Proof.
 induction p using Pos.peano_rect.
 - trivial.
 - change (N.pos (Pos.succ p)) with (N.succ (N.pos p)).
   rewrite N.mul_succ_r.
   change 10 at 2 with (Nat.iter 10%nat N.succ 0).
   rewrite ?nat_iter_S, nat_iter_0.
   rewrite !N.add_succ_r, N.add_0_r, !to_lu_succ, IHp.
   destruct (to_lu (N.pos p)); simpl; auto.
Qed.

Lemma of_lu_0 d : of_lu d = 0 <-> nztail d = Nil.
Proof.
 induction d; try simpl_of_lu; split; trivial; try discriminate;
 try (intros H; now apply N.eq_add_0 in H).
 - rewrite N.add_0_l. intros H.
   apply N.eq_mul_0_r in H; [|easy]. rewrite IHd in H.
   simpl. now rewrite H.
 - simpl. destruct (nztail d); try discriminate.
   now destruct IHd as [_ ->].
Qed.

Lemma to_of_lu_tenfold d :
 to_lu (of_lu d) = lnorm d ->
 to_lu (10 * of_lu d) = lnorm (D0 d).
Proof.
 intro IH.
 destruct (N.eq_dec (of_lu d) 0) as [H|H].
 - rewrite H. simpl. rewrite of_lu_0 in H.
   unfold lnorm. simpl. now rewrite H.
 - destruct (of_lu d) eqn:Eq; [easy| ].
   rewrite to_ldec_tenfold; auto. rewrite IH.
   rewrite <- Eq in H. rewrite of_lu_0 in H.
   unfold lnorm. simpl. now destruct (nztail d).
Qed.

Lemma Nadd_alt n m : n + m = Nat.iter (N.to_nat n) N.succ m.
Proof.
 destruct n. trivial.
 induction p using Pos.peano_rect.
 - now rewrite N.add_1_l.
 - change (N.pos (Pos.succ p)) with (N.succ (N.pos p)).
   now rewrite N.add_succ_l, IHp, N2Nat.inj_succ.
Qed.

Ltac simpl_to_nat := simpl N.to_nat; unfold Pos.to_nat; simpl Pos.iter_op.

Lemma to_of_lu d : to_lu (of_lu d) = lnorm d.
Proof.
 induction d; [reflexivity|..];
 simpl_of_lu; rewrite Nadd_alt; simpl_to_nat;
 rewrite ?nat_iter_S, nat_iter_0, ?to_lu_succ, to_of_lu_tenfold by assumption;
 unfold lnorm; simpl; destruct nztail; auto.
Qed.

(** Second bijection result *)

Lemma to_of (d:uint) : N.to_uint (Pos.of_uint d) = unorm d.
Proof.
 rewrite of_uint_alt.
 unfold N.to_uint, Pos.to_uint.
 destruct (of_lu (rev d)) eqn:H.
 - rewrite of_lu_0 in H. rewrite <- rev_lnorm_rev.
   unfold lnorm. now rewrite H.
 - change (Pos.to_little_uint p) with (to_lu (N.pos p)).
   rewrite <- H. rewrite to_of_lu. apply rev_lnorm_rev.
Qed.

(** Some consequences *)

Lemma to_uint_nonzero p : Pos.to_uint p <> zero.
Proof.
 intro E. generalize (of_to p). now rewrite E.
Qed.

Lemma to_uint_nonnil p : Pos.to_uint p <> Nil.
Proof.
 intros E. generalize (of_to p). now rewrite E.
Qed.

Lemma to_uint_inj p p' : Pos.to_uint p = Pos.to_uint p' -> p = p'.
Proof.
 intro E.
 assert (E' : N.pos p = N.pos p').
 { now rewrite <- (of_to p), <- (of_to p'), E. }
 now injection E'.
Qed.

Lemma to_uint_pos_surj d :
 unorm d<>zero -> exists p, Pos.to_uint p = unorm d.
Proof.
 intros.
 destruct (Pos.of_uint d) eqn:E.
 - destruct H. generalize (to_of d). now rewrite E.
 - exists p. generalize (to_of d). now rewrite E.
Qed.

Lemma of_uint_norm d : Pos.of_uint (unorm d) = Pos.of_uint d.
Proof.
 now induction d.
Qed.

Lemma of_inj d d' :
 Pos.of_uint d = Pos.of_uint d' -> unorm d = unorm d'.
Proof.
 intros. rewrite <- !to_of. now f_equal.
Qed.

Lemma of_iff d d' : Pos.of_uint d = Pos.of_uint d' <-> unorm d = unorm d'.
Proof.
 split. apply of_inj. intros E. rewrite <- of_uint_norm, E.
 apply of_uint_norm.
Qed.

End Unsigned.

(** Conversion from/to signed decimal numbers *)

Module Signed.

Lemma of_to (p:positive) : Pos.of_int (Pos.to_int p) = Some p.
Proof.
 unfold Pos.to_int, Pos.of_int, norm.
 now rewrite Unsigned.of_to.
Qed.

Lemma to_of (d:int)(p:positive) :
 Pos.of_int d = Some p -> Pos.to_int p = norm d.
Proof.
 unfold Pos.of_int.
 destruct d; [ | intros [=]].
 simpl norm. rewrite <- Unsigned.to_of.
 destruct (Pos.of_uint d); now intros [= <-].
Qed.

Lemma to_int_inj p p' : Pos.to_int p = Pos.to_int p' -> p = p'.
Proof.
 intro E.
 assert (E' : Some p = Some p').
 { now rewrite <- (of_to p), <- (of_to p'), E. }
 now injection E'.
Qed.

Lemma to_int_pos_surj d :
 unorm d <> zero -> exists p, Pos.to_int p = norm (Pos d).
Proof.
 simpl. unfold Pos.to_int. intros H.
 destruct (Unsigned.to_uint_pos_surj d H) as (p,Hp).
 exists p. now f_equal.
Qed.

Lemma of_int_norm d : Pos.of_int (norm d) = Pos.of_int d.
Proof.
 unfold Pos.of_int.
 destruct d.
 - simpl. now rewrite Unsigned.of_uint_norm.
 - simpl. now destruct (nzhead d) eqn:H.
Qed.

Lemma of_inj_pos d d' :
 Pos.of_int (Pos d) = Pos.of_int (Pos d') -> unorm d = unorm d'.
Proof.
 unfold Pos.of_int.
 destruct (Pos.of_uint d) eqn:Hd, (Pos.of_uint d') eqn:Hd';
  intros [=].
 - apply Unsigned.of_inj; now rewrite Hd, Hd'.
 - apply Unsigned.of_inj; rewrite Hd, Hd'; now f_equal.
Qed.

End Signed.
