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

Definition Zeven_bool (z:Z) :=
  match z with
    | Z0 => true
    | Zpos (xO _) => true
    | Zneg (xO _) => true
    | _ => false
  end.

Definition Zodd_bool (z:Z) :=
  match z with
    | Z0 => false
    | Zpos (xO _) => false
    | Zneg (xO _) => false
    | _ => true
  end.

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
(** * Definition of [Zdiv2] and properties wrt [Zeven] and [Zodd] *)

(** [Zdiv2] is defined on all [Z], but notice that for odd negative
  integers we have [n = 2*(Zdiv2 n)-1], hence it does not
  correspond to the usual Coq division [Zdiv], for which we would
  have here [n = 2*(n/2)+1]. Since [Zdiv2] performs rounding
  toward zero, it is rather a particular case of the alternative
  division [Zquot].
*)

Definition Zdiv2 (z:Z) :=
  match z with
    | 0 => 0
    | Zpos 1 => 0
    | Zpos p => Zpos (Pdiv2 p)
    | Zneg 1 => 0
    | Zneg p => Zneg (Pdiv2 p)
  end.

(** We also provide an alternative [Zdiv2'] performing round toward
  bottom, and hence corresponding to [Zdiv]. *)

Definition Zdiv2' a :=
 match a with
   | 0 => 0
   | Zpos 1 => 0
   | Zpos p => Zpos (Pdiv2 p)
   | Zneg p => Zneg (Pdiv2_up p)
 end.

Lemma Zdiv2'_odd : forall a,
 a = 2*(Zdiv2' a) + if Zodd_bool a then 1 else 0.
Proof.
 intros [ |[p|p| ]|[p|p|  ]]; simpl; trivial.
 f_equal. now rewrite xO_succ_permute, <-Ppred_minus, Ppred_succ.
Qed.

Lemma Zeven_div2 : forall n:Z, Zeven n -> n = 2 * Zdiv2 n.
Proof.
  intro x; destruct x.
  auto with arith.
  destruct p; auto with arith.
  intros. absurd (Zeven (Zpos (xI p))); red; auto with arith.
  intros. absurd (Zeven 1); red; auto with arith.
  destruct p; auto with arith.
  intros. absurd (Zeven (Zneg (xI p))); red; auto with arith.
  intros. absurd (Zeven (-1)); red; auto with arith.
Qed.

Lemma Zodd_div2 : forall n:Z, n >= 0 -> Zodd n -> n = 2 * Zdiv2 n + 1.
Proof.
  intro x; destruct x.
  intros. absurd (Zodd 0); red; auto with arith.
  destruct p; auto with arith.
  intros. absurd (Zodd (Zpos (xO p))); red; auto with arith.
  intros. absurd (Zneg p >= 0); red; auto with arith.
Qed.

Lemma Zodd_div2_neg :
  forall n:Z, n <= 0 -> Zodd n -> n = 2 * Zdiv2 n - 1.
Proof.
  intro x; destruct x.
  intros. absurd (Zodd 0); red; auto with arith.
  intros. absurd (Zneg p >= 0); red; auto with arith.
  destruct p; auto with arith.
  intros. absurd (Zodd (Zneg (xO p))); red; auto with arith.
Qed.

Lemma Z_modulo_2 :
  forall n:Z, {y : Z | n = 2 * y} + {y : Z | n = 2 * y + 1}.
Proof.
  intros x.
  elim (Zeven_odd_dec x); intro.
  left. split with (Zdiv2 x). exact (Zeven_div2 x a).
  right. generalize b; clear b; case x.
  intro b; inversion b.
  intro p; split with (Zdiv2 (Zpos p)). apply (Zodd_div2 (Zpos p)); trivial.
  unfold Zge, Zcompare; simpl; discriminate.
  intro p; split with (Zdiv2 (Zpred (Zneg p))).
  pattern (Zneg p) at 1; rewrite (Zsucc_pred (Zneg p)).
  pattern (Zpred (Zneg p)) at 1; rewrite (Zeven_div2 (Zpred (Zneg p))).
  reflexivity.
  apply Zeven_pred; assumption.
Qed.

Lemma Zsplit2 :
  forall n:Z,
    {p : Z * Z |
      let (x1, x2) := p in n = x1 + x2 /\ (x1 = x2 \/ x2 = x1 + 1)}.
Proof.
  intros x.
  elim (Z_modulo_2 x); intros [y Hy]; rewrite Zmult_comm in Hy;
    rewrite <- Zplus_diag_eq_mult_2 in Hy.
  exists (y, y); split.
  assumption.
  left; reflexivity.
  exists (y, (y + 1)%Z); split.
  rewrite Zplus_assoc; assumption.
  right; reflexivity.
Qed.


Theorem Zeven_ex: forall n, Zeven n -> exists m, n = 2 * m.
Proof.
  intro n; exists (Zdiv2 n); apply Zeven_div2; auto.
Qed.

Theorem Zodd_ex: forall n, Zodd n -> exists m, n = 2 * m + 1.
Proof.
  destruct n; intros.
  inversion H.
  exists (Zdiv2 (Zpos p)).
  apply Zodd_div2; simpl; auto; compute; inversion 1.
  exists (Zdiv2 (Zneg p) - 1).
  unfold Zminus.
  rewrite Zmult_plus_distr_r.
  rewrite <- Zplus_assoc.
  assert (Zneg p <= 0) by (compute; inversion 1).
  exact (Zodd_div2_neg _ H0 H).
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
  intros a b H1 H2; case Zeven_ex with (1 := H1); intros x H3; try rewrite H3; auto.
  case Zodd_ex with (1 := H2); intros y H4; try rewrite H4; auto.
  replace (2 * x + (2 * y + 1)) with (2 * (x + y) + 1); try apply Zodd_2p_plus_1; auto with zarith.
  rewrite Zmult_plus_distr_r, Zplus_assoc; auto.
Qed.

Theorem Zeven_plus_Zeven: forall a b,
 Zeven a -> Zeven b -> Zeven (a + b).
Proof.
  intros a b H1 H2; case Zeven_ex with (1 := H1); intros x H3; try rewrite H3; auto.
  case Zeven_ex with (1 := H2); intros y H4; try rewrite H4; auto.
  replace (2 * x + 2 * y) with (2 * (x + y)); try apply Zeven_2p; auto with zarith.
  apply Zmult_plus_distr_r; auto.
Qed.

Theorem Zodd_plus_Zeven: forall a b,
 Zodd a -> Zeven b -> Zodd (a + b).
Proof.
  intros a b H1 H2; rewrite Zplus_comm; apply Zeven_plus_Zodd; auto.
Qed.

Theorem Zodd_plus_Zodd: forall a b,
 Zodd a -> Zodd b -> Zeven (a + b).
Proof.
  intros a b H1 H2; case Zodd_ex with (1 := H1); intros x H3; try rewrite H3; auto.
  case Zodd_ex with (1 := H2); intros y H4; try rewrite H4; auto.
  replace ((2 * x + 1) + (2 * y + 1)) with (2 * (x + y + 1)); try apply Zeven_2p; auto.
  (* ring part *)
  do 2 rewrite Zmult_plus_distr_r; auto.
  repeat rewrite <- Zplus_assoc; f_equal.
  rewrite (Zplus_comm 1).
  repeat rewrite <- Zplus_assoc; auto.
Qed.

Theorem Zeven_mult_Zeven_l: forall a b,
 Zeven a -> Zeven (a * b).
Proof.
  intros a b H1; case Zeven_ex with (1 := H1); intros x H3; try rewrite H3; auto.
  replace (2 * x * b) with (2 * (x * b)); try apply Zeven_2p; auto with zarith.
  (* ring part *)
  apply Zmult_assoc.
Qed.

Theorem Zeven_mult_Zeven_r: forall a b,
 Zeven b -> Zeven (a * b).
Proof.
  intros a b H1; case Zeven_ex with (1 := H1); intros x H3; try rewrite H3; auto.
  replace (a * (2 * x)) with (2 * (x * a)); try apply Zeven_2p; auto.
  (* ring part *)
  rewrite (Zmult_comm x a).
  do 2 rewrite Zmult_assoc.
  rewrite (Zmult_comm 2 a); auto.
Qed.

Hint Rewrite Zmult_plus_distr_r Zmult_plus_distr_l
     Zplus_assoc Zmult_1_r Zmult_1_l : Zexpand.

Theorem Zodd_mult_Zodd: forall a b,
 Zodd a -> Zodd b -> Zodd (a * b).
Proof.
  intros a b H1 H2; case Zodd_ex with (1 := H1); intros x H3; try rewrite H3; auto.
  case Zodd_ex with (1 := H2); intros y H4; try rewrite H4; auto.
  replace ((2 * x + 1) * (2 * y + 1)) with (2 * (2 * x * y + x + y) + 1); try apply Zodd_2p_plus_1; auto.
  (* ring part *)
  autorewrite with Zexpand; f_equal.
  repeat rewrite <- Zplus_assoc; f_equal.
  repeat rewrite <- Zmult_assoc; f_equal.
  repeat rewrite Zmult_assoc; f_equal; apply Zmult_comm.
Qed.

(* for compatibility *)
Close Scope Z_scope.
