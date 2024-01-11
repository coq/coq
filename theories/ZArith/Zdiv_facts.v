(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinInt Zdiv Znumtheory Lia.
Local Open Scope Z_scope.

Module Z.

Lemma cong_mul_cancel_r_coprime a b m (Hm : m <> 0) (Hb : Z.gcd b m = 1)
  (H : (a * b) mod m = 0) : a mod m = 0.
Proof.
  apply Zmod_divide in H; trivial; [].
  rewrite Z.mul_comm in H; apply Gauss, Zdivide_mod in H; trivial.
  apply rel_prime_sym, Zgcd_1_rel_prime; trivial.
Qed.

Lemma diveq_iff c a b :
  (b = 0 /\ c = 0 \/ c*b <= a < c*b + b \/ c*b + b < a <= c*b) <-> a/b = c.
Proof.
  destruct (Z.eqb_spec b 0); [subst; rewrite Zdiv_0_r; intuition lia|].
  rewrite <-(Z.sub_move_0_r (_/_)),  <-(Z.add_opp_r (_/_)).
  rewrite <-Z.div_add, Z.div_small_iff; lia.
Qed.

Lemma mod_diveq_iff c a b :
  (b = 0 \/ c*b <= a < c*b + b \/ c*b + b < a <= c*b) <-> a mod b = a-b*c.
Proof.
  destruct (Z.eqb_spec b 0); [subst; rewrite Zmod_0_r; intuition lia|].
  rewrite Z.mod_eq by trivial; pose proof diveq_iff c a b; nia.
Qed.

Definition mod_diveq c a b := proj1 (mod_diveq_iff c a b).

Definition diveq c a b := proj1 (diveq_iff c a b).

Lemma mod_mod_pow a b n m : 0 <= n < m -> (a mod b^m) mod b^n = a mod b^n.
Proof.
  intro; apply mod_mod_divide. exists (b^(m-n)).
  rewrite <-Z.pow_add_r; f_equal; try lia.
Qed.

Lemma div_mod_l_mul_r a b c (Hb : 0 <> b) (Hc : 0 < c) :
  a mod (b * c) / b = (a / b) mod c.
Proof.
  rewrite 2Z.mod_eq by lia.
  rewrite <-Z.add_opp_r, <-Z.mul_opp_r, <-Z.mul_assoc, Z.mul_comm.
  rewrite Z.div_add, Z.div_div; lia.
Qed.

Lemma div_mod_l_pow2_r a b m n (Hb : 0 < b) (H : 0 <= n <= m) :
  a mod b ^ m / b ^ n = a / b ^ n mod b ^ (m - n).
Proof.
  replace m with (n+(m-n)) at 1 by lia; rewrite Z.pow_add_r by lia.
  rewrite div_mod_l_mul_r; lia.
Qed.

Lemma gcd_of_N a b : Z.gcd (Z.of_N a) (Z.of_N b) = Z.of_N (N.gcd a b).
Proof. case a, b; trivial. Qed.

Lemma mod_pow_l a b c : (a mod c)^b mod c = ((a ^ b) mod c).
Proof.
  destruct (Z.ltb_spec b 0) as [|Hb]. { rewrite !Z.pow_neg_r; trivial. }
  destruct (Z.eqb_spec c 0) as [|Hc]. { subst. rewrite !Zmod_0_r; trivial. }
  generalize dependent b; eapply natlike_ind; trivial; intros x Hx IH.
  rewrite !Z.pow_succ_r, <-Z.mul_mod_idemp_r, IH, Z.mul_mod_idemp_l, Z.mul_mod_idemp_r; trivial.
Qed.

Lemma coprime_mul a b m : Z.gcd a m = 1 -> Z.gcd b m = 1 -> Z.gcd (a * b) m = 1.
Proof.
  intros.
  apply Zgcd_1_rel_prime, rel_prime_sym, rel_prime_mult;
  apply rel_prime_sym, Zgcd_1_rel_prime; trivial.
Qed.

End Z.
