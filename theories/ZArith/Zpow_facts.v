(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import ZArith_base.
Require Import ZArithRing.
Require Import Zcomplements.
Require Export Zpower.
Require Import Zdiv.
Require Import Znumtheory.
Open Local Scope Z_scope.

Lemma Zpower_pos_1_r: forall x, Zpower_pos x 1 = x.
Proof.
  intros x; unfold Zpower_pos; simpl; auto with zarith.
Qed.

Lemma Zpower_pos_1_l: forall p, Zpower_pos 1 p = 1.
Proof.
  induction p.
  (* xI *)
  rewrite xI_succ_xO, <-Pplus_diag, Pplus_one_succ_l.
  repeat rewrite Zpower_pos_is_exp.
  rewrite Zpower_pos_1_r, IHp; auto.
  (* xO *)
  rewrite <- Pplus_diag.
  repeat rewrite Zpower_pos_is_exp.
  rewrite IHp; auto.
  (* xH *)
  rewrite Zpower_pos_1_r; auto.
Qed.

Lemma Zpower_pos_0_l: forall p, Zpower_pos 0 p = 0.
Proof.
  induction p.
  change (xI p) with (1 + (xO p))%positive.
  rewrite Zpower_pos_is_exp, Zpower_pos_1_r; auto.
  rewrite <- Pplus_diag.
  rewrite Zpower_pos_is_exp, IHp; auto.
  rewrite Zpower_pos_1_r; auto.
Qed.

Lemma Zpower_pos_pos: forall x p,
  0 < x -> 0 < Zpower_pos x p.
Proof.
  induction p; intros.
  (* xI *)
  rewrite xI_succ_xO, <-Pplus_diag, Pplus_one_succ_l.
  repeat rewrite Zpower_pos_is_exp.
  rewrite Zpower_pos_1_r.
  repeat apply Zmult_lt_0_compat; auto.
  (* xO *)
  rewrite <- Pplus_diag.
  repeat rewrite Zpower_pos_is_exp.
  repeat apply Zmult_lt_0_compat; auto.
  (* xH *)
  rewrite Zpower_pos_1_r; auto.
Qed.


Theorem Zpower_1_r: forall z, z^1 = z.
Proof.
  exact Zpower_pos_1_r.
Qed.

Theorem Zpower_1_l: forall z, 0 <= z -> 1^z = 1.
Proof.
  destruct z; simpl; auto.
  intros; apply Zpower_pos_1_l.
  intros; compute in H; elim H; auto.
Qed.

Theorem Zpower_0_l: forall z, z<>0 -> 0^z = 0.
Proof.
  destruct z; simpl; auto with zarith.
  intros; apply Zpower_pos_0_l.
Qed.

Theorem Zpower_0_r: forall z, z^0 = 1.
Proof.
  simpl; auto.
Qed.

Theorem Zpower_2: forall z, z^2 = z * z.
Proof.
  intros; ring.
Qed.

Theorem Zpower_gt_0: forall x y,
  0 < x -> 0 <= y -> 0 < x^y.
Proof.
  destruct y; simpl; auto with zarith.
  intros; apply Zpower_pos_pos; auto.
  intros; compute in H0; elim H0; auto.
Qed.

Theorem Zpower_Zabs: forall a b,  Zabs (a^b) = (Zabs a)^b.
Proof.
  intros a b; case (Zle_or_lt 0 b).
  intros Hb; pattern b; apply natlike_ind; auto with zarith.
  intros x Hx Hx1; unfold Zsucc.
  (repeat rewrite Zpower_exp); auto with zarith.
  rewrite Zabs_Zmult; rewrite Hx1.
  f_equal; auto.
  replace (a ^ 1) with a; auto.
  simpl; unfold Zpower_pos; simpl; rewrite Zmult_1_r; auto.
  simpl; unfold Zpower_pos; simpl; rewrite Zmult_1_r; auto.
  case b; simpl; auto with zarith.
  intros p Hp; discriminate.
Qed.

Theorem Zpower_Zsucc: forall p n, 0 <= n -> p^(Zsucc n) = p * p^n.
Proof.
  intros p n H.
  unfold Zsucc; rewrite Zpower_exp; auto with zarith.
  rewrite Zpower_1_r; apply Zmult_comm.
Qed.

Theorem Zpower_mult: forall p q r, 0 <= q -> 0 <= r -> p^(q*r) = (p^q)^r.
Proof.
  intros p q r H1 H2; generalize H2; pattern r; apply natlike_ind; auto.
  intros H3; rewrite Zmult_0_r; repeat rewrite Zpower_exp_0; auto.
  intros r1 H3 H4 H5.
  unfold Zsucc; rewrite Zpower_exp; auto with zarith.
  rewrite <- H4; try rewrite Zpower_1_r; try rewrite <- Zpower_exp; try f_equal; auto with zarith.
  ring.
  apply Zle_ge; replace 0 with (0 * r1); try apply Zmult_le_compat_r; auto.
Qed.

Theorem Zpower_le_monotone: forall a b c,
 0 < a -> 0 <= b <= c -> a^b <= a^c.
Proof.
  intros a b c H (H1, H2).
  rewrite <- (Zmult_1_r (a ^ b)); replace c with (b + (c - b)); auto with zarith.
  rewrite Zpower_exp; auto with zarith.
  apply Zmult_le_compat_l; auto with zarith.
  assert (0 < a ^ (c - b)); auto with zarith.
  apply Zpower_gt_0; auto with zarith.
  apply Zlt_le_weak; apply Zpower_gt_0; auto with zarith.
Qed.

Theorem Zpower_lt_monotone: forall a b c,
 1 < a -> 0 <= b < c -> a^b < a^c.
Proof.
  intros a b c H (H1, H2).
  rewrite <- (Zmult_1_r (a ^ b)); replace c with (b + (c - b)); auto with zarith.
  rewrite Zpower_exp; auto with zarith.
  apply Zmult_lt_compat_l; auto with zarith.
  apply Zpower_gt_0; auto with zarith.
  assert (0 < a ^ (c - b)); auto with zarith.
  apply Zpower_gt_0; auto with zarith.
  apply Zlt_le_trans with (a ^1); auto with zarith.
  rewrite Zpower_1_r; auto with zarith.
  apply Zpower_le_monotone; auto with zarith.
Qed.

Theorem Zpower_gt_1 : forall x y,
  1 < x -> 0 < y -> 1 < x^y.
Proof.
  intros x y H1 H2.
  replace 1 with (x ^ 0) by apply Zpower_0_r.
  apply Zpower_lt_monotone; auto with zarith.
Qed.

Theorem Zpower_ge_0: forall x y, 0 <= x -> 0 <= x^y.
Proof.
  intros x y; case y; auto with zarith.
  simpl ; auto with zarith.
  intros p H1; assert (H: 0 <= Zpos p); auto with zarith.
  generalize H; pattern (Zpos p); apply natlike_ind; auto with zarith.
  intros p1 H2 H3 _; unfold Zsucc; rewrite Zpower_exp; simpl; auto with zarith.
  apply Zmult_le_0_compat; auto with zarith.
  generalize H1; case x; compute; intros; auto; try discriminate.
Qed.

Theorem Zpower_le_monotone2:
   forall a b c, 0 < a -> b <= c -> a^b <= a^c.
Proof.
  intros a b c H H2.
  destruct (Z_le_gt_dec 0 b).
  apply Zpower_le_monotone; auto.
  replace (a^b) with 0.
  destruct (Z_le_gt_dec 0 c).
  destruct (Zle_lt_or_eq _ _ z0).
  apply Zlt_le_weak;apply Zpower_gt_0;trivial.
  rewrite <- H0;simpl;auto with zarith.
  replace (a^c) with 0. auto with zarith.
  destruct c;trivial;unfold Zgt in z0;discriminate z0.
  destruct b;trivial;unfold Zgt in z;discriminate z.
Qed.

Theorem Zmult_power: forall p q r, 0 <= r ->
  (p*q)^r = p^r * q^r.
Proof.
  intros p q r H1; generalize H1; pattern r; apply natlike_ind; auto.
  clear r H1; intros r H1 H2 H3.
  unfold Zsucc; rewrite Zpower_exp; auto with zarith.
  rewrite H2; repeat rewrite Zpower_exp; auto with zarith; ring.
Qed.

Hint Resolve Zpower_ge_0 Zpower_gt_0: zarith.

Theorem Zpower_le_monotone3: forall a b c,
 0 <= c -> 0 <= a <= b -> a^c <= b^c.
Proof.
  intros a b c H (H1, H2).
  generalize H; pattern c; apply natlike_ind; auto.
  intros x HH HH1 _; unfold Zsucc; repeat rewrite Zpower_exp; auto with zarith.
  repeat rewrite Zpower_1_r.
  apply Zle_trans with (a^x * b); auto with zarith.
Qed.

Lemma Zpower_le_monotone_inv: forall a b c,
  1 < a -> 0 < b -> a^b <= a^c -> b <= c.
Proof.
  intros a b c H H0 H1.
  destruct (Z_le_gt_dec b c);trivial.
  assert (2 <= a^b).
   apply Zle_trans with (2^b).
   pattern 2 at 1;replace 2 with (2^1);trivial.
   apply Zpower_le_monotone;auto with zarith.
   apply Zpower_le_monotone3;auto with zarith.
  assert (c > 0).
  destruct (Z_le_gt_dec 0 c);trivial.
  destruct (Zle_lt_or_eq _ _ z0);auto with zarith.
  rewrite <- H3 in H1;simpl in H1; exfalso;omega.
  destruct c;try discriminate z0. simpl in H1. exfalso;omega.
  assert (H4 := Zpower_lt_monotone a c b H). exfalso;omega.
Qed.

Theorem Zpower_nat_Zpower: forall p q, 0 <= q ->
 p^q = Zpower_nat p (Zabs_nat q).
Proof.
  intros p1 q1; case q1; simpl.
  intros _; exact (refl_equal _).
  intros p2 _; apply Zpower_pos_nat.
  intros p2 H1; case H1; auto.
Qed.

Theorem Zpower2_lt_lin: forall n, 0 <= n -> n < 2^n.
Proof.
  intros n; apply (natlike_ind (fun n => n < 2 ^n)); clear n.
  simpl; auto with zarith.
  intros n H1 H2; unfold Zsucc.
  case (Zle_lt_or_eq _ _ H1); clear H1; intros H1.
  apply Zle_lt_trans with (n + n); auto with zarith.
  rewrite Zpower_exp; auto with zarith.
  rewrite Zpower_1_r.
  assert (tmp: forall p, p * 2 = p + p); intros; try ring;
  rewrite tmp; auto with zarith.
  subst n; simpl; unfold Zpower_pos; simpl; auto with zarith.
Qed.

Theorem Zpower2_le_lin: forall n, 0 <= n -> n <= 2^n.
Proof.
  intros; apply Zlt_le_weak; apply Zpower2_lt_lin; auto.
Qed.

Lemma Zpower2_Psize :
  forall n p, Zpos p < 2^(Z_of_nat n) <-> (Psize p <= n)%nat.
Proof.
  induction n.
  destruct p; split; intros H; discriminate H || inversion H.
  destruct p; simpl Psize.
  rewrite inj_S, Zpower_Zsucc; auto with zarith.
  rewrite Zpos_xI; specialize IHn with p; omega.
  rewrite inj_S, Zpower_Zsucc; auto with zarith.
  rewrite Zpos_xO; specialize IHn with p; omega.
  split; auto with arith.
  intros _; apply Zpower_gt_1; auto with zarith.
  rewrite inj_S; generalize (Zle_0_nat n); omega.
Qed.

(** * Zpower and modulo *)

Theorem Zpower_mod: forall p q n, 0 < n ->
 (p^q) mod n = ((p mod n)^q) mod n.
Proof.
  intros p q n Hn; case (Zle_or_lt 0 q); intros H1.
  generalize H1; pattern q; apply natlike_ind; auto.
  intros q1 Hq1 Rec _; unfold Zsucc; repeat rewrite Zpower_exp; repeat rewrite Zpower_1_r; auto with zarith.
  rewrite (fun x => (Zmult_mod x p)); try rewrite Rec; auto with zarith.
  rewrite (fun x y => (Zmult_mod (x ^y))); try f_equal; auto with zarith.
  f_equal; auto; apply sym_equal; apply Zmod_mod; auto with zarith.
  generalize H1; case q; simpl; auto.
  intros; discriminate.
Qed.

(** A direct way to compute Zpower modulo **)

Fixpoint Zpow_mod_pos (a: Z)(m: positive)(n : Z) {struct m} : Z :=
  match m with
   | xH => a mod n
   | xO m' =>
      let z := Zpow_mod_pos a m' n in
      match z with
       | 0 => 0
       | _ => (z * z) mod n
      end
   | xI m' =>
      let z := Zpow_mod_pos a m' n in
      match z with
       | 0 => 0
       | _ => (z * z * a) mod n
      end
  end.

Definition Zpow_mod a m n :=
  match m with
   | 0 => 1
   | Zpos p => Zpow_mod_pos a p n
   | Zneg p => 0
  end.

Theorem Zpow_mod_pos_correct: forall a m n, 0 < n ->
 Zpow_mod_pos a m n = (Zpower_pos a m) mod n.
Proof.
  intros a m; elim m; simpl; auto.
  intros p Rec n H1; rewrite xI_succ_xO, Pplus_one_succ_r, <-Pplus_diag; auto.
  repeat rewrite Zpower_pos_is_exp; auto.
  repeat rewrite Rec; auto.
  rewrite Zpower_pos_1_r.
  repeat rewrite (fun x => (Zmult_mod x a)); auto with zarith.
  rewrite (Zmult_mod (Zpower_pos a p)); auto with zarith.
  case (Zpower_pos a p mod n); auto.
  intros p Rec n H1; rewrite <- Pplus_diag; auto.
  repeat rewrite Zpower_pos_is_exp; auto.
  repeat rewrite Rec; auto.
  rewrite (Zmult_mod (Zpower_pos a p)); auto with zarith.
  case (Zpower_pos a p mod n); auto.
  unfold Zpower_pos; simpl; rewrite Zmult_1_r; auto with zarith.
Qed.

Theorem Zpow_mod_correct: forall a m n, 1 < n -> 0 <= m ->
 Zpow_mod a m n = (a ^ m) mod n.
Proof.
  intros a m n; case m; simpl.
  intros; apply sym_equal; apply Zmod_small; auto with zarith.
  intros; apply Zpow_mod_pos_correct; auto with zarith.
  intros p H H1; case H1; auto.
Qed.

(* Complements about power and number theory. *)

Lemma Zpower_divide: forall p q, 0 < q -> (p | p ^ q).
Proof.
  intros p q H; exists (p ^(q - 1)).
  pattern p at 3; rewrite <- (Zpower_1_r p); rewrite <- Zpower_exp; try f_equal; auto with zarith.
Qed.

Theorem rel_prime_Zpower_r: forall i p q, 0 < i ->
 rel_prime p q -> rel_prime p (q^i).
Proof.
  intros i p q Hi Hpq; generalize Hi; pattern i; apply natlike_ind; auto with zarith; clear i Hi.
  intros H; contradict H; auto with zarith.
  intros i Hi Rec _; rewrite Zpower_Zsucc; auto.
  apply rel_prime_mult; auto.
  case Zle_lt_or_eq with (1 := Hi); intros Hi1; subst; auto.
  rewrite Zpower_0_r; apply rel_prime_sym; apply rel_prime_1.
Qed.

Theorem rel_prime_Zpower: forall i j p q, 0 <= i ->  0 <= j ->
 rel_prime p q -> rel_prime (p^i) (q^j).
Proof.
  intros i j p q Hi; generalize Hi j p q; pattern i; apply natlike_ind; auto with zarith; clear i Hi j p q.
  intros _ j p q H H1; rewrite Zpower_0_r; apply rel_prime_1.
  intros n Hn Rec _ j p q Hj Hpq.
  rewrite Zpower_Zsucc; auto.
  case Zle_lt_or_eq with (1 := Hj); intros Hj1; subst.
  apply rel_prime_sym; apply rel_prime_mult; auto.
  apply rel_prime_sym; apply rel_prime_Zpower_r; auto with arith.
  apply rel_prime_sym; apply Rec; auto.
  rewrite Zpower_0_r; apply rel_prime_sym; apply rel_prime_1.
Qed.

Theorem prime_power_prime: forall p q n, 0 <= n ->
 prime p -> prime q -> (p | q^n)  -> p = q.
Proof.
  intros p q n Hn Hp Hq; pattern n; apply natlike_ind; auto; clear n Hn.
  rewrite Zpower_0_r; intros.
  assert (2<=p) by (apply prime_ge_2; auto).
  assert (p<=1) by (apply Zdivide_le; auto with zarith).
  omega.
  intros n1 H H1.
  unfold Zsucc; rewrite Zpower_exp; try rewrite Zpower_1_r; auto with zarith.
  assert (2<=p) by (apply prime_ge_2; auto).
  assert (2<=q) by (apply prime_ge_2; auto).
  intros H3; case prime_mult with (2 := H3); auto.
  intros; apply prime_div_prime; auto.
Qed.

Theorem Zdivide_power_2: forall x p n, 0 <= n -> 0 <= x -> prime p ->
 (x | p^n) -> exists m, x = p^m.
Proof.
  intros x p n Hn Hx; revert p n Hn; generalize Hx.
  pattern x; apply Z_lt_induction; auto.
  clear x Hx; intros x IH Hx p n Hn Hp H.
  case Zle_lt_or_eq with (1 := Hx); auto; clear Hx; intros Hx; subst.
  case (Zle_lt_or_eq 1 x); auto with zarith; clear Hx; intros Hx; subst.
  (* x > 1 *)
  case (prime_dec x); intros H2.
  exists 1; rewrite Zpower_1_r; apply prime_power_prime with n; auto.
  case not_prime_divide with (2 := H2); auto.
  intros p1 ((H3, H4), (q1, Hq1)); subst.
  case (IH p1) with p n; auto with zarith.
  apply Zdivide_trans with (2 := H); exists q1; auto with zarith.
  intros r1 Hr1.
  case (IH q1) with p n; auto with zarith.
  case (Zle_lt_or_eq 0 q1).
  apply Zmult_le_0_reg_r with p1; auto with zarith.
  split; auto with zarith.
  pattern q1 at 1; replace q1 with (q1 * 1); auto with zarith.
  apply Zmult_lt_compat_l; auto with zarith.
  intros H5; subst; contradict Hx; auto with zarith.
  apply Zmult_le_0_reg_r with p1; auto with zarith.
  apply Zdivide_trans with (2 := H); exists p1; auto with zarith.
  intros r2 Hr2; exists (r2 + r1); subst.
  apply sym_equal; apply Zpower_exp.
  generalize Hx; case r2; simpl; auto with zarith.
  intros; red; simpl; intros; discriminate.
  generalize H3; case r1; simpl; auto with zarith.
  intros; red; simpl; intros; discriminate.
  (* x = 1 *)
  exists 0; rewrite Zpower_0_r; auto.
  (* x = 0 *)
  exists n; destruct H; rewrite Zmult_0_r in H; auto.
Qed.

(** * Zsquare: a direct definition of [z^2] *)

Fixpoint Psquare (p: positive): positive :=
  match p with
   | xH => xH
   | xO p => xO (xO (Psquare p))
   | xI p => xI (xO (Pplus (Psquare p) p))
  end.

Definition Zsquare p :=
  match p with
   | Z0 => Z0
   | Zpos p => Zpos (Psquare p)
   | Zneg p => Zpos (Psquare p)
  end.

Theorem Psquare_correct: forall p, Psquare p = (p * p)%positive.
Proof.
  induction p; simpl; auto; f_equal; rewrite IHp.
  apply trans_equal with (xO p + xO (p*p))%positive; auto.
  rewrite (Pplus_comm (xO p)); auto.
  rewrite Pmult_xI_permute_r; rewrite Pplus_assoc.
  f_equal; auto.
  symmetry; apply Pplus_diag.
  symmetry; apply Pmult_xO_permute_r.
Qed.

Theorem Zsquare_correct: forall p, Zsquare p = p * p.
Proof.
  intro p; case p; simpl; auto; intros p1; rewrite Psquare_correct; auto.
Qed.
