(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * HexadecimalPos

    Proofs that conversions between hexadecimal numbers and [positive]
    are bijections. *)

Require Import Hexadecimal HexadecimalFacts PArith NArith.

Module Unsigned.

Local Open Scope N.

(** A direct version of [of_little_uint] *)
Fixpoint of_lu (d:uint) : N :=
  match d with
  | Nil => 0
  | D0 d => 0x10 * of_lu d
  | D1 d => 0x1 + 0x10 * of_lu d
  | D2 d => 0x2 + 0x10 * of_lu d
  | D3 d => 0x3 + 0x10 * of_lu d
  | D4 d => 0x4 + 0x10 * of_lu d
  | D5 d => 0x5 + 0x10 * of_lu d
  | D6 d => 0x6 + 0x10 * of_lu d
  | D7 d => 0x7 + 0x10 * of_lu d
  | D8 d => 0x8 + 0x10 * of_lu d
  | D9 d => 0x9 + 0x10 * of_lu d
  | Da d => 0xa + 0x10 * of_lu d
  | Db d => 0xb + 0x10 * of_lu d
  | Dc d => 0xc + 0x10 * of_lu d
  | Dd d => 0xd + 0x10 * of_lu d
  | De d => 0xe + 0x10 * of_lu d
  | Df d => 0xf + 0x10 * of_lu d
  end.

Definition hd d :=
  match d with
  | Nil => 0x0
  | D0 _ => 0x0
  | D1 _ => 0x1
  | D2 _ => 0x2
  | D3 _ => 0x3
  | D4 _ => 0x4
  | D5 _ => 0x5
  | D6 _ => 0x6
  | D7 _ => 0x7
  | D8 _ => 0x8
  | D9 _ => 0x9
  | Da _ => 0xa
  | Db _ => 0xb
  | Dc _ => 0xc
  | Dd _ => 0xd
  | De _ => 0xe
  | Df _ => 0xf
  end.

Definition tl d :=
  match d with
  | Nil => d
  | D0 d | D1 d | D2 d | D3 d | D4 d | D5 d | D6 d | D7 d | D8 d | D9 d
  | Da d | Db d | Dc d | Dd d | De d | Df d => d
  end.

Lemma of_lu_eqn d :
  of_lu d = hd d + 0x10 * (of_lu (tl d)).
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
  | Da d => N.succ (usize d)
  | Db d => N.succ (usize d)
  | Dc d => N.succ (usize d)
  | Dd d => N.succ (usize d)
  | De d => N.succ (usize d)
  | Df d => N.succ (usize d)
  end.

Lemma of_lu_revapp d d' :
  of_lu (revapp d d') =
    of_lu (rev d) + of_lu d' * 0x10^usize d.
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
  Pos.of_hex_uint_acc d acc = Pos.of_hex_uint_acc (tl d) (Nadd (hd d) (0x10*acc)).
Proof.
  destruct d; simpl; trivial. now destruct 1.
Qed.

Lemma of_uint_acc_rev d acc :
  Npos (Pos.of_hex_uint_acc d acc) =
    of_lu (rev d) + (Npos acc) * 0x10^usize d.
Proof.
  revert acc.
  induction d; intros; simpl usize;
  [ simpl; now rewrite Pos.mul_1_r | .. ];
  rewrite N.pow_succ_r';
  unfold rev; simpl revapp; try rewrite of_lu_revapp; simpl of_lu;
  rewrite of_uint_acc_eqn by easy; simpl tl; simpl hd;
  rewrite IHd, Nadd_simpl; ring.
Qed.

Lemma of_uint_alt d : Pos.of_hex_uint d = of_lu (rev d).
Proof.
  induction d; simpl; trivial; unfold rev; simpl revapp;
  rewrite of_lu_revapp; simpl of_lu; try apply of_uint_acc_rev.
  rewrite IHd. ring.
Qed.

Lemma of_lu_rev d : Pos.of_hex_uint (rev d) = of_lu d.
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

Lemma of_to (p:positive) : Pos.of_hex_uint (Pos.to_hex_uint p) = Npos p.
Proof.
  unfold Pos.to_hex_uint.
  rewrite of_lu_rev.
  induction p; simpl; trivial.
  - now rewrite of_lu_succ_double, IHp.
  - now rewrite of_lu_double, IHp.
Qed.

(** The other direction *)

Definition to_lu n :=
  match n with
  | N0 => Hexadecimal.zero
  | Npos p => Pos.to_little_hex_uint p
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

Lemma to_lhex_tenfold p :
  to_lu (0x10 * Npos p) = D0 (to_lu (Npos p)).
Proof.
  induction p using Pos.peano_rect.
  - trivial.
  - change (N.pos (Pos.succ p)) with (N.succ (N.pos p)).
    rewrite N.mul_succ_r.
    change 0x10 with (Nat.iter 0x10%nat N.succ 0) at 2.
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
  to_lu (0x10 * of_lu d) = lnorm (D0 d).
Proof.
  intro IH.
  destruct (N.eq_dec (of_lu d) 0) as [H|H].
  - rewrite H. simpl. rewrite of_lu_0 in H.
    unfold lnorm. simpl. now rewrite H.
  - destruct (of_lu d) eqn:Eq; [easy| ].
    rewrite to_lhex_tenfold; auto. rewrite IH.
    rewrite <- Eq in H. rewrite of_lu_0 in H.
    unfold lnorm. simpl. now destruct (nztail d).
Qed.

Lemma Nadd_alt n m : n + m = Nat.iter (N.to_nat n) N.succ m.
Proof.
  destruct n. 1:trivial.
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
  unfold lnorm; simpl nztail; destruct nztail; reflexivity.
Qed.

(** Second bijection result *)

Lemma to_of (d:uint) : N.to_hex_uint (Pos.of_hex_uint d) = unorm d.
Proof.
  rewrite of_uint_alt.
  unfold N.to_hex_uint, Pos.to_hex_uint.
  destruct (of_lu (rev d)) eqn:H.
  - rewrite of_lu_0 in H. rewrite <- rev_lnorm_rev.
    unfold lnorm. now rewrite H.
  - change (Pos.to_little_hex_uint p) with (to_lu (N.pos p)).
    rewrite <- H. rewrite to_of_lu. apply rev_lnorm_rev.
Qed.

(** Some consequences *)

Lemma to_uint_nonzero p : Pos.to_hex_uint p <> zero.
Proof.
  intro E. generalize (of_to p). now rewrite E.
Qed.

Lemma to_uint_nonnil p : Pos.to_hex_uint p <> Nil.
Proof.
  intros E. generalize (of_to p). now rewrite E.
Qed.

Lemma to_uint_inj p p' : Pos.to_hex_uint p = Pos.to_hex_uint p' -> p = p'.
Proof.
  intro E.
  assert (E' : N.pos p = N.pos p').
  { now rewrite <- (of_to p), <- (of_to p'), E. }
  now injection E'.
Qed.

Lemma to_uint_pos_surj d :
  unorm d<>zero -> exists p, Pos.to_hex_uint p = unorm d.
Proof.
  intros.
  destruct (Pos.of_hex_uint d) eqn:E.
  - destruct H. generalize (to_of d). now rewrite E.
  - exists p. generalize (to_of d). now rewrite E.
Qed.

Lemma of_uint_norm d : Pos.of_hex_uint (unorm d) = Pos.of_hex_uint d.
Proof.
  now induction d.
Qed.

Lemma of_inj d d' :
  Pos.of_hex_uint d = Pos.of_hex_uint d' -> unorm d = unorm d'.
Proof.
  intros. rewrite <- !to_of. now f_equal.
Qed.

Lemma of_iff d d' : Pos.of_hex_uint d = Pos.of_hex_uint d' <-> unorm d = unorm d'.
Proof.
  split.
  - apply of_inj.
  - intros E. rewrite <- of_uint_norm, E.
    apply of_uint_norm.
Qed.

(* various lemmas *)

Lemma nztail_to_hex_uint p :
  let (h, n) := Hexadecimal.nztail (Pos.to_hex_uint p) in
  Npos p = Pos.of_hex_uint h * 0x10^(N.of_nat n).
Proof.
  rewrite <-(of_to p), <-(rev_rev (Pos.to_hex_uint p)), of_lu_rev.
  unfold Hexadecimal.nztail.
  rewrite rev_rev.
  induction (rev (Pos.to_hex_uint p)); [reflexivity| |
    now simpl N.of_nat; simpl N.pow; rewrite N.mul_1_r, of_lu_rev..].
  revert IHu.
  set (t := _ u); case t; clear t; intros u0 n H.
  rewrite of_lu_eqn; unfold hd, tl.
  rewrite N.add_0_l, H, Nat2N.inj_succ, N.pow_succ_r'; ring.
Qed.

Definition double d := rev (Little.double (rev d)).

Lemma double_unorm d : double (unorm d) = unorm (double d).
Proof.
  unfold double.
  rewrite <-!rev_lnorm_rev, !rev_rev, <-!to_of_lu, of_lu_double.
  now case of_lu; [now simpl|]; intro p; induction p.
Qed.

Lemma double_nzhead d : double (nzhead d) = nzhead (double d).
Proof.
  unfold double.
  rewrite <-!rev_nztail_rev, !rev_rev.
  apply f_equal; generalize (rev d); clear d; intro d.
  cut (Little.double (nztail d) = nztail (Little.double d)
       /\ Little.succ_double (nztail d) = nztail (Little.succ_double d)).
  { now simpl. }
  now induction d;
    [|split; simpl; rewrite <-?(proj1 IHd), <-?(proj2 IHd); case nztail..].
Qed.

Lemma of_hex_uint_double d :
  Pos.of_hex_uint (double d) = N.double (Pos.of_hex_uint d).
Proof.
  now unfold double; rewrite of_lu_rev, of_lu_double, <-of_lu_rev, rev_rev.
Qed.

End Unsigned.

(** Conversion from/to signed decimal numbers *)

Module Signed.

Lemma of_to (p:positive) : Pos.of_hex_int (Pos.to_hex_int p) = Some p.
Proof.
  unfold Pos.to_hex_int, Pos.of_hex_int, norm.
  now rewrite Unsigned.of_to.
Qed.

Lemma to_of (d:int)(p:positive) :
  Pos.of_hex_int d = Some p -> Pos.to_hex_int p = norm d.
Proof.
  unfold Pos.of_hex_int.
  destruct d; [ | intros [=]].
  simpl norm. rewrite <- Unsigned.to_of.
  destruct (Pos.of_hex_uint d); now intros [= <-].
Qed.

Lemma to_int_inj p p' : Pos.to_hex_int p = Pos.to_hex_int p' -> p = p'.
Proof.
  intro E.
  assert (E' : Some p = Some p').
  { now rewrite <- (of_to p), <- (of_to p'), E. }
  now injection E'.
Qed.

Lemma to_int_pos_surj d :
  unorm d <> zero -> exists p, Pos.to_hex_int p = norm (Pos d).
Proof.
  simpl. unfold Pos.to_hex_int. intros H.
  destruct (Unsigned.to_uint_pos_surj d H) as (p,Hp).
  exists p. now f_equal.
Qed.

Lemma of_int_norm d : Pos.of_hex_int (norm d) = Pos.of_hex_int d.
Proof.
  unfold Pos.of_int.
  destruct d.
  - simpl. now rewrite Unsigned.of_uint_norm.
  - simpl. now destruct (nzhead d) eqn:H.
Qed.

Lemma of_inj_pos d d' :
  Pos.of_hex_int (Pos d) = Pos.of_hex_int (Pos d') -> unorm d = unorm d'.
Proof.
  unfold Pos.of_hex_int.
  destruct (Pos.of_hex_uint d) eqn:Hd, (Pos.of_hex_uint d') eqn:Hd';
    intros [=].
  - apply Unsigned.of_inj; now rewrite Hd, Hd'.
  - apply Unsigned.of_inj; rewrite Hd, Hd'; now f_equal.
Qed.

End Signed.
