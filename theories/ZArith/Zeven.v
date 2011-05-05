(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinInt.

Open Scope Z_scope.

(*******************************************************************)
(** About parity: even and odd predicates on Z, division by 2 on Z *)

(***************************************************)
(** * [Zeven], [Zodd] and their related properties *)

Definition Zeven (z:Z) :=
  match z with
    | Z0 => True
    | Zpos (xO _) => True
    | Zneg (xO _) => True
    | _ => False
  end.

Definition Zodd (z:Z) :=
  match z with
    | Zpos xH => True
    | Zneg xH => True
    | Zpos (xI _) => True
    | Zneg (xI _) => True
    | _ => False
  end.

Notation Zeven_bool := Z.even (only parsing).
Notation Zodd_bool := Z.odd (only parsing).

Lemma Zeven_bool_iff : forall n, Zeven_bool n = true <-> Zeven n.
Proof.
 destruct n as [|p|p]; try destruct p; simpl in *; split; easy.
Qed.

Lemma Zodd_bool_iff : forall n, Zodd_bool n = true <-> Zodd n.
Proof.
 destruct n as [|p|p]; try destruct p; simpl in *; split; easy.
Qed.

Lemma Zodd_even_bool : forall n, Zodd_bool n = negb (Zeven_bool n).
Proof.
 destruct n as [|p|p]; trivial; now destruct p.
Qed.

Lemma Zeven_odd_bool : forall n, Zeven_bool n = negb (Zodd_bool n).
Proof.
 destruct n as [|p|p]; trivial; now destruct p.
Qed.

Definition Zeven_odd_dec : forall z:Z, {Zeven z} + {Zodd z}.
Proof.
  intro z. case z;
  [ left; compute; trivial
    | intro p; case p; intros;
      (right; compute; exact I) || (left; compute; exact I)
    | intro p; case p; intros;
      (right; compute; exact I) || (left; compute; exact I) ].
Defined.

Definition Zeven_dec : forall z:Z, {Zeven z} + {~ Zeven z}.
Proof.
  intro z. case z;
  [ left; compute; trivial
    | intro p; case p; intros;
      (left; compute; exact I) || (right; compute; trivial)
    | intro p; case p; intros;
      (left; compute; exact I) || (right; compute; trivial) ].
Defined.

Definition Zodd_dec : forall z:Z, {Zodd z} + {~ Zodd z}.
Proof.
  intro z. case z;
  [ right; compute; trivial
    | intro p; case p; intros;
      (left; compute; exact I) || (right; compute; trivial)
    | intro p; case p; intros;
      (left; compute; exact I) || (right; compute; trivial) ].
Defined.

Lemma Zeven_not_Zodd : forall n:Z, Zeven n -> ~ Zodd n.
Proof.
  intro z; destruct z; [ idtac | destruct p | destruct p ]; compute;
    trivial.
Qed.

Lemma Zodd_not_Zeven : forall n:Z, Zodd n -> ~ Zeven n.
Proof.
  intro z; destruct z; [ idtac | destruct p | destruct p ]; compute;
    trivial.
Qed.

Lemma Zeven_Sn : forall n:Z, Zodd n -> Zeven (Zsucc n).
Proof.
  intro z; destruct z; unfold Zsucc;
    [ idtac | destruct p | destruct p ]; simpl;
      trivial.
  unfold Pdouble_minus_one; case p; simpl; auto.
Qed.

Lemma Zodd_Sn : forall n:Z, Zeven n -> Zodd (Zsucc n).
Proof.
  intro z; destruct z; unfold Zsucc;
    [ idtac | destruct p | destruct p ]; simpl;
      trivial.
  unfold Pdouble_minus_one; case p; simpl; auto.
Qed.

Lemma Zeven_pred : forall n:Z, Zodd n -> Zeven (Zpred n).
Proof.
  intro z; destruct z; unfold Zpred;
    [ idtac | destruct p | destruct p ]; simpl;
      trivial.
  unfold Pdouble_minus_one; case p; simpl; auto.
Qed.

Lemma Zodd_pred : forall n:Z, Zeven n -> Zodd (Zpred n).
Proof.
  intro z; destruct z; unfold Zpred;
    [ idtac | destruct p | destruct p ]; simpl;
      trivial.
  unfold Pdouble_minus_one; case p; simpl; auto.
Qed.

Hint Unfold Zeven Zodd: zarith.

Lemma Zeven_bool_succ : forall n, Zeven_bool (Zsucc n) = Zodd_bool n.
Proof.
 destruct n as [ |p|p]; trivial; destruct p as [p|p| ]; trivial.
 now destruct p.
Qed.

Lemma Zeven_bool_pred : forall n, Zeven_bool (Zpred n) = Zodd_bool n.
Proof.
 destruct n as [ |p|p]; trivial; destruct p as [p|p| ]; trivial.
 now destruct p.
Qed.

Lemma Zodd_bool_succ : forall n, Zodd_bool (Zsucc n) = Zeven_bool n.
Proof.
 destruct n as [ |p|p]; trivial; destruct p as [p|p| ]; trivial.
 now destruct p.
Qed.

Lemma Zodd_bool_pred : forall n, Zodd_bool (Zpred n) = Zeven_bool n.
Proof.
 destruct n as [ |p|p]; trivial; destruct p as [p|p| ]; trivial.
 now destruct p.
Qed.

(******************************************************************)
(** * Definition of [Zquot2], [Zdiv2] and properties wrt [Zeven]
  and [Zodd] *)

Notation Zdiv2 := Z.div2 (only parsing).
Notation Zquot2 := Z.quot2 (only parsing).

(** Properties of [Zdiv2] *)

Lemma Zdiv2_odd_eqn : forall n,
 n = 2*(Zdiv2 n) + if Zodd_bool n then 1 else 0.
Proof.
 intros [ |[p|p| ]|[p|p|  ]]; simpl; trivial.
 f_equal. symmetry. apply Pos.pred_double_succ.
Qed.

Lemma Zeven_div2 : forall n:Z, Zeven n -> n = 2 * Zdiv2 n.
Proof.
 intros n Hn. apply Zeven_bool_iff in Hn.
 pattern n at 1.
 now rewrite (Zdiv2_odd_eqn n), Zodd_even_bool, Hn, Zplus_0_r.
Qed.

Lemma Zodd_div2 : forall n:Z, Zodd n -> n = 2 * Zdiv2 n + 1.
Proof.
 intros n Hn. apply Zodd_bool_iff in Hn.
 pattern n at 1. now rewrite (Zdiv2_odd_eqn n), Hn.
Qed.

(** Properties of [Zquot2] *)

Lemma Zquot2_odd_eqn : forall n,
 n = 2*(Zquot2 n) + if Zodd_bool n then Zsgn n else 0.
Proof.
 intros [ |[p|p| ]|[p|p|  ]]; simpl; trivial.
Qed.

Lemma Zeven_quot2 : forall n:Z, Zeven n -> n = 2 * Zquot2 n.
Proof.
 intros n Hn. apply Zeven_bool_iff in Hn.
 pattern n at 1.
 now rewrite (Zquot2_odd_eqn n), Zodd_even_bool, Hn, Zplus_0_r.
Qed.

Lemma Zodd_quot2 : forall n:Z, n >= 0 -> Zodd n -> n = 2 * Zquot2 n + 1.
Proof.
 intros n Hn Hn'. apply Zodd_bool_iff in Hn'.
 pattern n at 1. rewrite (Zquot2_odd_eqn n), Hn'. f_equal.
 destruct n; (now destruct Hn) || easy.
Qed.

Lemma Zodd_quot2_neg :
  forall n:Z, n <= 0 -> Zodd n -> n = 2 * Zquot2 n - 1.
Proof.
 intros n Hn Hn'. apply Zodd_bool_iff in Hn'.
 pattern n at 1. rewrite (Zquot2_odd_eqn n), Hn'. unfold Zminus. f_equal.
 destruct n; (now destruct Hn) || easy.
Qed.

(** More properties of parity *)

Lemma Z_modulo_2 :
  forall n:Z, {y : Z | n = 2 * y} + {y : Z | n = 2 * y + 1}.
Proof.
 intros n.
 destruct (Zeven_odd_dec n) as [Hn|Hn].
 left. exists (Zdiv2 n). exact (Zeven_div2 n Hn).
 right. exists (Zdiv2 n). exact (Zodd_div2 n Hn).
Qed.

Lemma Zsplit2 :
  forall n:Z,
    {p : Z * Z |
      let (x1, x2) := p in n = x1 + x2 /\ (x1 = x2 \/ x2 = x1 + 1)}.
Proof.
 intros n.
 destruct (Z_modulo_2 n) as [(y,Hy)|(y,Hy)];
  rewrite Zmult_comm, <- Zplus_diag_eq_mult_2 in Hy.
 exists (y, y). split. assumption. now left.
 exists (y, y + 1). split. now rewrite Zplus_assoc. now right.
Qed.

Theorem Zeven_ex: forall n, Zeven n -> exists m, n = 2 * m.
Proof.
  intro n; exists (Zdiv2 n); apply Zeven_div2; auto.
Qed.

Theorem Zodd_ex: forall n, Zodd n -> exists m, n = 2 * m + 1.
Proof.
  intro n; exists (Zdiv2 n); apply Zodd_div2; auto.
Qed.

Theorem Zeven_2p: forall p, Zeven (2 * p).
Proof.
  destruct p; simpl; auto.
Qed.

Theorem Zodd_2p_plus_1: forall p, Zodd (2 * p + 1).
Proof.
  destruct p; simpl; auto.
  destruct p; simpl; auto.
Qed.

Theorem Zeven_ex_iff : forall n, Zeven n <-> exists m, n = 2*m.
Proof.
 split. apply Zeven_ex. intros (m,->). apply Zeven_2p.
Qed.

Theorem Zodd_ex_iff : forall n, Zodd n <-> exists m, n = 2*m + 1.
Proof.
 split. apply Zodd_ex. intros (m,->). apply Zodd_2p_plus_1.
Qed.

Theorem Zeven_plus_Zodd: forall a b,
 Zeven a -> Zodd b -> Zodd (a + b).
Proof.
  intros a b Ha Hb.
  destruct (Zeven_ex a) as (x,->), (Zodd_ex b) as (y,->); trivial.
  rewrite Zplus_assoc, <- Zmult_plus_distr_r.
  apply Zodd_2p_plus_1.
Qed.

Theorem Zeven_plus_Zeven: forall a b,
 Zeven a -> Zeven b -> Zeven (a + b).
Proof.
  intros a b Ha Hb.
  destruct (Zeven_ex a) as (x,->), (Zeven_ex b) as (y,->); trivial.
  rewrite <- Zmult_plus_distr_r.
  apply Zeven_2p.
Qed.

Theorem Zodd_plus_Zeven: forall a b,
 Zodd a -> Zeven b -> Zodd (a + b).
Proof.
  intros a b Ha Hb; rewrite Zplus_comm; apply Zeven_plus_Zodd; auto.
Qed.

Theorem Zodd_plus_Zodd: forall a b,
 Zodd a -> Zodd b -> Zeven (a + b).
Proof.
  intros a b Ha Hb.
  destruct (Zodd_ex a) as (x,->), (Zodd_ex b) as (y,->); trivial.
  rewrite <- Zplus_assoc, (Zplus_comm 1), <- Zplus_assoc.
  change (1+1) with (2*1). rewrite <- 2 Zmult_plus_distr_r.
  apply Zeven_2p.
Qed.

Theorem Zeven_mult_Zeven_l: forall a b,
 Zeven a -> Zeven (a * b).
Proof.
  intros a b Ha.
  destruct (Zeven_ex a) as (x,->); trivial.
  rewrite <- Zmult_assoc.
  apply Zeven_2p.
Qed.

Theorem Zeven_mult_Zeven_r: forall a b,
 Zeven b -> Zeven (a * b).
Proof.
  intros a b Hb. rewrite Zmult_comm. now apply Zeven_mult_Zeven_l.
Qed.

Hint Rewrite Zmult_plus_distr_r Zmult_plus_distr_l
     Zplus_assoc Zmult_1_r Zmult_1_l : Zexpand.

Theorem Zodd_mult_Zodd: forall a b,
 Zodd a -> Zodd b -> Zodd (a * b).
Proof.
  intros a b Ha Hb.
  destruct (Zodd_ex a) as (x,->), (Zodd_ex b) as (y,->); trivial.
  rewrite Zmult_plus_distr_l, Zmult_1_l.
  rewrite <- Zmult_assoc, Zplus_assoc, <- Zmult_plus_distr_r.
  apply Zodd_2p_plus_1.
Qed.

(* for compatibility *)
Close Scope Z_scope.
