(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Binary Integers : Parity and Division by Two *)
(** Initial author : Pierre Crégut (CNET, Lannion, France) *)

(** THIS FILE IS DEPRECATED.
    It is now almost entirely made of compatibility formulations
    for results already present in BinInt.Z. *)

Require Import BinInt.

Open Scope Z_scope.

(** Historical formulation of even and odd predicates, based on
    case analysis. We now rather recommend using [Z.Even] and
    [Z.Odd], which are based on the exist predicate. *)

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

Lemma Zeven_equiv z : Zeven z <-> Z.Even z.
Proof.
 rewrite <- Z.even_spec.
 destruct z as [|p|p]; try destruct p; simpl; intuition.
Qed.

Lemma Zodd_equiv z : Zodd z <-> Z.Odd z.
Proof.
 rewrite <- Z.odd_spec.
 destruct z as [|p|p]; try destruct p; simpl; intuition.
Qed.

Theorem Zeven_ex_iff n : Zeven n <-> exists m, n = 2*m.
Proof (Zeven_equiv n).

Theorem Zodd_ex_iff n : Zodd n <-> exists m, n = 2*m + 1.
Proof (Zodd_equiv n).

(** Boolean tests of parity (now in BinInt.Z) *)

Notation Zeven_bool := Z.even (only parsing).
Notation Zodd_bool := Z.odd (only parsing).

Lemma Zeven_bool_iff n : Z.even n = true <-> Zeven n.
Proof.
 now rewrite Z.even_spec, Zeven_equiv.
Qed.

Lemma Zodd_bool_iff n : Z.odd n = true <-> Zodd n.
Proof.
 now rewrite Z.odd_spec, Zodd_equiv.
Qed.

Ltac boolify_even_odd := rewrite <- ?Zeven_bool_iff, <- ?Zodd_bool_iff.

Lemma Zodd_even_bool n : Z.odd n = negb (Z.even n).
Proof.
 symmetry. apply Z.negb_even.
Qed.

Lemma Zeven_odd_bool n : Z.even n = negb (Z.odd n).
Proof.
 symmetry. apply Z.negb_odd.
Qed.

Definition Zeven_odd_dec n : {Zeven n} + {Zodd n}.
Proof.
 destruct n as [|p|p]; try destruct p; simpl; (now left) || (now right).
Defined.

Definition Zeven_dec n : {Zeven n} + {~ Zeven n}.
Proof.
 destruct n as [|p|p]; try destruct p; simpl; (now left) || (now right).
Defined.

Definition Zodd_dec n : {Zodd n} + {~ Zodd n}.
Proof.
 destruct n as [|p|p]; try destruct p; simpl; (now left) || (now right).
Defined.

Lemma Zeven_not_Zodd n : Zeven n -> ~ Zodd n.
Proof.
 boolify_even_odd. rewrite <- Z.negb_odd. destruct Z.odd; intuition.
Qed.

Lemma Zodd_not_Zeven n : Zodd n -> ~ Zeven n.
Proof.
 boolify_even_odd. rewrite <- Z.negb_odd. destruct Z.odd; intuition.
Qed.

Lemma Zeven_Sn n : Zodd n -> Zeven (Z.succ n).
Proof.
 boolify_even_odd. now rewrite Z.even_succ.
Qed.

Lemma Zodd_Sn n : Zeven n -> Zodd (Z.succ n).
Proof.
 boolify_even_odd. now rewrite Z.odd_succ.
Qed.

Lemma Zeven_pred n : Zodd n -> Zeven (Z.pred n).
Proof.
 boolify_even_odd. now rewrite Z.even_pred.
Qed.

Lemma Zodd_pred n : Zeven n -> Zodd (Z.pred n).
Proof.
 boolify_even_odd. now rewrite Z.odd_pred.
Qed.

Hint Unfold Zeven Zodd: zarith.

Notation Zeven_bool_succ := Z.even_succ (only parsing).
Notation Zeven_bool_pred := Z.even_pred (only parsing).
Notation Zodd_bool_succ := Z.odd_succ (only parsing).
Notation Zodd_bool_pred := Z.odd_pred (only parsing).

(******************************************************************)
(** * Definition of [Z.quot2], [Z.div2] and properties wrt [Zeven]
  and [Zodd] *)

Notation Zdiv2 := Z.div2 (compat "8.7").
Notation Zquot2 := Z.quot2 (compat "8.7").

(** Properties of [Z.div2] *)

Lemma Zdiv2_odd_eqn n : n = 2*(Z.div2 n) + if Z.odd n then 1 else 0.
Proof (Z.div2_odd n).

Lemma Zeven_div2 n : Zeven n -> n = 2 * Z.div2 n.
Proof.
 boolify_even_odd. rewrite <- Z.negb_odd, Bool.negb_true_iff.
 intros Hn. rewrite (Zdiv2_odd_eqn n) at 1. now rewrite Hn, Z.add_0_r.
Qed.

Lemma Zodd_div2 n : Zodd n -> n = 2 * Z.div2 n + 1.
Proof.
 boolify_even_odd.
 intros Hn. rewrite (Zdiv2_odd_eqn n) at 1. now rewrite Hn.
Qed.

(** Properties of [Z.quot2] *)

(** TODO: move to Numbers someday *)

Lemma Zquot2_odd_eqn n : n = 2*(Z.quot2 n) + if Z.odd n then Z.sgn n else 0.
Proof.
 now destruct n as [ |[p|p| ]|[p|p| ]].
Qed.

Lemma Zeven_quot2 n : Zeven n -> n = 2 * Z.quot2 n.
Proof.
 intros Hn. apply Zeven_bool_iff in Hn.
 rewrite (Zquot2_odd_eqn n) at 1.
 now rewrite Zodd_even_bool, Hn, Z.add_0_r.
Qed.

Lemma Zodd_quot2 n : n >= 0 -> Zodd n -> n = 2 * Z.quot2 n + 1.
Proof.
 intros Hn Hn'. apply Zodd_bool_iff in Hn'.
 rewrite (Zquot2_odd_eqn n) at 1. rewrite Hn'. f_equal.
 destruct n; (now destruct Hn) || easy.
Qed.

Lemma Zodd_quot2_neg n : n <= 0 -> Zodd n -> n = 2 * Z.quot2 n - 1.
Proof.
 intros Hn Hn'. apply Zodd_bool_iff in Hn'.
 rewrite (Zquot2_odd_eqn n) at 1; rewrite Hn'. unfold Z.sub. f_equal.
 destruct n; (now destruct Hn) || easy.
Qed.

Lemma Zquot2_opp n : Z.quot2 (-n) = - Z.quot2 n.
Proof.
 now destruct n as [ |[p|p| ]|[p|p| ]].
Qed.

Lemma Zquot2_quot n : Z.quot2 n = n ÷ 2.
Proof.
 assert (AUX : forall m, 0 < m -> Z.quot2 m = m ÷ 2).
  {
   intros m Hm.
   apply Z.quot_unique with (if Z.odd m then Z.sgn m else 0).
   now apply Z.lt_le_incl.
   rewrite Z.sgn_pos by trivial.
   destruct (Z.odd m); now split.
   apply Zquot2_odd_eqn.
  }
 destruct (Z.lt_trichotomy 0 n) as [POS|[NUL|NEG]].
 - now apply AUX.
 - now subst.
 - apply Z.opp_inj. rewrite <- Z.quot_opp_l, <- Zquot2_opp.
   apply AUX. now destruct n. easy.
Qed.

(** More properties of parity *)

Lemma Z_modulo_2 n : {y | n = 2 * y} + {y | n = 2 * y + 1}.
Proof.
 destruct (Zeven_odd_dec n) as [Hn|Hn].
 - left. exists (Z.div2 n). exact (Zeven_div2 n Hn).
 - right. exists (Z.div2 n). exact (Zodd_div2 n Hn).
Qed.

Lemma Zsplit2 n :
 {p : Z * Z | let (x1, x2) := p in n = x1 + x2 /\ (x1 = x2 \/ x2 = x1 + 1)}.
Proof.
 destruct (Z_modulo_2 n) as [(y,Hy)|(y,Hy)];
  rewrite <- Z.add_diag in Hy.
 - exists (y, y). split. assumption. now left.
 - exists (y, y + 1). split. now rewrite Z.add_assoc. now right.
Qed.

Theorem Zeven_ex n : Zeven n -> exists m, n = 2 * m.
Proof.
 exists (Z.div2 n); apply Zeven_div2; auto.
Qed.

Theorem Zodd_ex n : Zodd n -> exists m, n = 2 * m + 1.
Proof.
 exists (Z.div2 n); apply Zodd_div2; auto.
Qed.

Theorem Zeven_2p p : Zeven (2 * p).
Proof.
 now destruct p.
Qed.

Theorem Zodd_2p_plus_1 p : Zodd (2 * p + 1).
Proof.
 destruct p as [|p|p]; now try destruct p.
Qed.

Theorem Zeven_plus_Zodd a b : Zeven a -> Zodd b -> Zodd (a + b).
Proof.
 boolify_even_odd. rewrite <- Z.negb_odd, Bool.negb_true_iff.
 intros Ha Hb. now rewrite Z.odd_add, Ha, Hb.
Qed.

Theorem Zeven_plus_Zeven a b : Zeven a -> Zeven b -> Zeven (a + b).
Proof.
 boolify_even_odd. intros Ha Hb. now rewrite Z.even_add, Ha, Hb.
Qed.

Theorem Zodd_plus_Zeven a b : Zodd a -> Zeven b -> Zodd (a + b).
Proof.
 intros. rewrite Z.add_comm. now apply Zeven_plus_Zodd.
Qed.

Theorem Zodd_plus_Zodd a b : Zodd a -> Zodd b -> Zeven (a + b).
Proof.
 boolify_even_odd. rewrite <- 2 Z.negb_even, 2 Bool.negb_true_iff.
 intros Ha Hb. now rewrite Z.even_add, Ha, Hb.
Qed.

Theorem Zeven_mult_Zeven_l a b : Zeven a -> Zeven (a * b).
Proof.
 boolify_even_odd. intros Ha. now rewrite Z.even_mul, Ha.
Qed.

Theorem Zeven_mult_Zeven_r a b : Zeven b -> Zeven (a * b).
Proof.
 intros. rewrite Z.mul_comm. now apply Zeven_mult_Zeven_l.
Qed.

Theorem Zodd_mult_Zodd a b : Zodd a -> Zodd b -> Zodd (a * b).
Proof.
 boolify_even_odd. intros Ha Hb. now rewrite Z.odd_mul, Ha, Hb.
Qed.

(* for compatibility *)
Close Scope Z_scope.
