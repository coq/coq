(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import ZArith_base.
Require Import ZArithRing.
Require Import Zcomplements.
Require Import Zdiv.
Require Import Wf_nat.
Open Local Scope Z_scope.

(** This file contains some notions of number theory upon Z numbers:
     - a divisibility predicate [Zdivide]
     - a gcd predicate [gcd]
     - Euclid algorithm [euclid]
     - a relatively prime predicate [rel_prime]
     - a prime predicate [prime]
     - an efficient [Zgcd] function
*)

(** * Divisibility *)

Inductive Zdivide (a b:Z) : Prop :=
    Zdivide_intro : forall q:Z, b = q * a -> Zdivide a b.

(** Syntax for divisibility *)

Notation "( a | b )" := (Zdivide a b) (at level 0) : Z_scope.

(** Results concerning divisibility*)

Lemma Zdivide_refl : forall a:Z, (a | a).
Proof.
  intros; apply Zdivide_intro with 1; ring.
Qed.

Lemma Zone_divide : forall a:Z, (1 | a).
Proof.
  intros; apply Zdivide_intro with a; ring.
Qed.

Lemma Zdivide_0 : forall a:Z, (a | 0).
Proof.
  intros; apply Zdivide_intro with 0; ring.
Qed.

Hint Resolve Zdivide_refl Zone_divide Zdivide_0: zarith.

Lemma Zmult_divide_compat_l : forall a b c:Z, (a | b) -> (c * a | c * b).
Proof.
  simple induction 1; intros; apply Zdivide_intro with q.
  rewrite H0; ring.
Qed.

Lemma Zmult_divide_compat_r : forall a b c:Z, (a | b) -> (a * c | b * c).
Proof.
  intros a b c; rewrite (Zmult_comm a c); rewrite (Zmult_comm b c).
  apply Zmult_divide_compat_l; trivial.
Qed.

Hint Resolve Zmult_divide_compat_l Zmult_divide_compat_r: zarith.

Lemma Zdivide_plus_r : forall a b c:Z, (a | b) -> (a | c) -> (a | b + c).
Proof.
  simple induction 1; intros q Hq; simple induction 1; intros q' Hq'.
  apply Zdivide_intro with (q + q').
  rewrite Hq; rewrite Hq'; ring.
Qed.

Lemma Zdivide_opp_r : forall a b:Z, (a | b) -> (a | - b).
Proof.
  simple induction 1; intros; apply Zdivide_intro with (- q).
  rewrite H0; ring.
Qed.

Lemma Zdivide_opp_r_rev : forall a b:Z, (a | - b) -> (a | b).
Proof.
  intros; replace b with (- - b). apply Zdivide_opp_r; trivial. ring.
Qed.

Lemma Zdivide_opp_l : forall a b:Z, (a | b) -> (- a | b).
Proof.
  simple induction 1; intros; apply Zdivide_intro with (- q).
  rewrite H0; ring.
Qed.

Lemma Zdivide_opp_l_rev : forall a b:Z, (- a | b) -> (a | b).
Proof.
  intros; replace a with (- - a). apply Zdivide_opp_l; trivial. ring.
Qed.

Lemma Zdivide_minus_l : forall a b c:Z, (a | b) -> (a | c) -> (a | b - c).
Proof.
  simple induction 1; intros q Hq; simple induction 1; intros q' Hq'.
  apply Zdivide_intro with (q - q').
  rewrite Hq; rewrite Hq'; ring.
Qed.

Lemma Zdivide_mult_l : forall a b c:Z, (a | b) -> (a | b * c).
Proof.
  simple induction 1; intros q Hq; apply Zdivide_intro with (q * c).
  rewrite Hq; ring.
Qed.

Lemma Zdivide_mult_r : forall a b c:Z, (a | c) -> (a | b * c).
Proof.
  simple induction 1; intros q Hq; apply Zdivide_intro with (q * b).
  rewrite Hq; ring.
Qed.

Lemma Zdivide_factor_r : forall a b:Z, (a | a * b).
Proof.
  intros; apply Zdivide_intro with b; ring.
Qed.

Lemma Zdivide_factor_l : forall a b:Z, (a | b * a).
Proof.
  intros; apply Zdivide_intro with b; ring.
Qed.

Hint Resolve Zdivide_plus_r Zdivide_opp_r Zdivide_opp_r_rev Zdivide_opp_l
  Zdivide_opp_l_rev Zdivide_minus_l Zdivide_mult_l Zdivide_mult_r
  Zdivide_factor_r Zdivide_factor_l: zarith.

(** Auxiliary result. *)

Lemma Zmult_one : forall x y:Z, x >= 0 -> x * y = 1 -> x = 1.
Proof.
  intros x y H H0; destruct (Zmult_1_inversion_l _ _ H0) as [Hpos| Hneg].
  assumption.
  rewrite Hneg in H; simpl in H.
  contradiction (Zle_not_lt 0 (-1)).
    apply Zge_le; assumption.
    apply Zorder.Zlt_neg_0.
Qed.

(** Only [1] and [-1] divide [1]. *)

Lemma Zdivide_1 : forall x:Z, (x | 1) -> x = 1 \/ x = -1.
Proof.
  simple induction 1; intros.
  elim (Z_lt_ge_dec 0 x); [ left | right ].
  apply Zmult_one with q; auto with zarith; rewrite H0; ring.
  assert (- x = 1); auto with zarith.
  apply Zmult_one with (- q); auto with zarith; rewrite H0; ring.
Qed.

(** If [a] divides [b] and [b] divides [a] then [a] is [b] or [-b]. *)

Lemma Zdivide_antisym : forall a b:Z, (a | b) -> (b | a) -> a = b \/ a = - b.
Proof.
  simple induction 1; intros.
  inversion H1.
  rewrite H0 in H2; clear H H1.
  case (Z_zerop a); intro.
  left; rewrite H0; rewrite e; ring.
  assert (Hqq0 : q0 * q = 1).
  apply Zmult_reg_l with a.
  assumption.
  ring_simplify.
  pattern a at 2 in |- *; rewrite H2; ring.
  assert (q | 1).
  rewrite <- Hqq0; auto with zarith.
  elim (Zdivide_1 q H); intros.
  rewrite H1 in H0; left; omega.
  rewrite H1 in H0; right; omega.
Qed.

Theorem Zdivide_trans: forall a b c, (a | b) -> (b | c) ->  (a | c).
Proof.
  intros a b c [d H1] [e H2]; exists (d * e); auto with zarith.
  rewrite H2; rewrite H1; ring.
Qed.

(** If [a] divides [b] and [b<>0] then [|a| <= |b|]. *)

Lemma Zdivide_bounds : forall a b:Z, (a | b) -> b <> 0 -> Zabs a <= Zabs b.
Proof.
  simple induction 1; intros.
  assert (Zabs b = Zabs q * Zabs a).
  subst; apply Zabs_Zmult.
  rewrite H2.
  assert (H3 := Zabs_pos q).
  assert (H4 := Zabs_pos a).
  assert (Zabs q * Zabs a >= 1 * Zabs a); auto with zarith.
  apply Zmult_ge_compat; auto with zarith.
  elim (Z_lt_ge_dec (Zabs q) 1); [ intros | auto with zarith ].
  assert (Zabs q = 0).
  omega.
  assert (q = 0).
  rewrite <- (Zabs_Zsgn q).
  rewrite H5; auto with zarith.
  subst q; omega.
Qed.

(** [Zdivide] can be expressed using [Zmod]. *)

Lemma Zmod_divide : forall a b, b<>0 -> a mod b = 0 -> (b | a).
Proof.
 intros a b NZ EQ.
 apply Zdivide_intro with (a/b).
 rewrite (Z_div_mod_eq_full a b NZ) at 1.
 rewrite EQ; ring.
Qed.

Lemma Zdivide_mod : forall a b, (b | a) -> a mod b = 0.
Proof.
  intros a b (c,->); apply Z_mod_mult.
Qed.

(** [Zdivide] is hence decidable *)

Lemma Zdivide_dec : forall a b:Z, {(a | b)} + {~ (a | b)}.
Proof.
  intros a b; elim (Ztrichotomy_inf a 0).
  (* a<0 *)
  intros H; elim H; intros.
  case (Z_eq_dec (b mod - a) 0).
  left; apply Zdivide_opp_l_rev; apply Zmod_divide; auto with zarith.
  intro H1; right; intro; elim H1; apply Zdivide_mod; auto with zarith.
  (* a=0 *)
  case (Z_eq_dec b 0); intro.
  left; subst; auto with zarith.
  right; subst; intro H0; inversion H0; omega.
  (* a>0 *)
  intro H; case (Z_eq_dec (b mod a) 0).
  left; apply Zmod_divide; auto with zarith.
  intro H1; right; intro; elim H1; apply Zdivide_mod; auto with zarith.
Qed.

Theorem Zdivide_Zdiv_eq: forall a b : Z,
 0 < a -> (a | b) ->  b = a * (b / a).
Proof.
  intros a b Hb Hc.
  pattern b at 1; rewrite (Z_div_mod_eq b a); auto with zarith.
  rewrite (Zdivide_mod b a); auto with zarith.
Qed.

Theorem Zdivide_Zdiv_eq_2: forall a b c : Z,
 0 < a -> (a | b) -> (c * b)/a = c * (b / a).
Proof.
  intros a b c H1 H2.
  inversion H2 as [z Hz].
  rewrite Hz; rewrite Zmult_assoc.
  repeat rewrite Z_div_mult; auto with zarith.
Qed.

Theorem Zdivide_Zabs_l: forall a b, (Zabs a | b) ->  (a | b).
Proof.
  intros a b [x H]; subst b.
  pattern (Zabs a); apply Zabs_intro.
  exists (- x); ring.
  exists x; ring.
Qed.

Theorem Zdivide_Zabs_inv_l: forall a b, (a | b) ->  (Zabs a | b).
Proof.
  intros a b [x H]; subst b.
  pattern (Zabs a); apply Zabs_intro.
  exists (- x);  ring.
  exists x; ring.
Qed.

Theorem Zdivide_le: forall a b : Z,
 0 <= a -> 0 < b -> (a | b) ->  a <= b.
Proof.
  intros a b H1 H2 [q H3]; subst b.
  case (Zle_lt_or_eq 0 a); auto with zarith; intros H3.
  case (Zle_lt_or_eq 0 q); auto with zarith.
  apply (Zmult_le_0_reg_r a); auto with zarith.
  intros H4; apply Zle_trans with (1 * a); auto with zarith.
  intros H4; subst q; omega.
Qed.

Theorem Zdivide_Zdiv_lt_pos: forall a b : Z,
 1 < a -> 0 < b -> (a | b) ->  0 < b / a < b .
Proof.
  intros a b H1 H2 H3; split.
  apply Zmult_lt_reg_r with a; auto with zarith.
  rewrite (Zmult_comm (Zdiv b a)); rewrite <- Zdivide_Zdiv_eq; auto with zarith.
  apply Zmult_lt_reg_r with a; auto with zarith.
  repeat rewrite (fun x => Zmult_comm x a); auto with zarith.
  rewrite <- Zdivide_Zdiv_eq; auto with zarith.
  pattern b at 1; replace b with (1 * b); auto with zarith.
  apply Zmult_lt_compat_r; auto with zarith.
Qed.

Lemma Zmod_div_mod: forall n m a, 0 < n -> 0 < m ->
 (n | m) -> a mod n = (a mod m) mod n.
Proof.
  intros n m a H1 H2 H3.
  pattern a at 1; rewrite (Z_div_mod_eq a m); auto with zarith.
  case H3; intros q Hq; pattern m at 1; rewrite Hq.
  rewrite (Zmult_comm q).
  rewrite Zplus_mod; auto with zarith.
  rewrite <- Zmult_assoc; rewrite Zmult_mod; auto with zarith.
  rewrite Z_mod_same; try rewrite Zmult_0_l; auto with zarith.
  rewrite (Zmod_small 0); auto with zarith.
  rewrite Zplus_0_l; rewrite Zmod_mod; auto with zarith.
Qed.

Lemma Zmod_divide_minus: forall a b c : Z, 0 < b ->
 a mod b = c -> (b | a - c).
Proof.
  intros a b c H H1; apply Zmod_divide; auto with zarith.
  rewrite Zminus_mod; auto with zarith.
  rewrite H1; pattern c at 1; rewrite <- (Zmod_small c b); auto with zarith.
  rewrite Zminus_diag; apply Zmod_small; auto with zarith.
  subst; apply Z_mod_lt; auto with zarith.
Qed.

Lemma Zdivide_mod_minus: forall a b c : Z, 0 <= c < b ->
 (b | a - c) -> a mod b = c.
Proof.
  intros a b c (H1, H2) H3; assert (0 < b); try apply Zle_lt_trans with c; auto.
  replace a with ((a - c) + c); auto with zarith.
  rewrite Zplus_mod; auto with zarith.
  rewrite (Zdivide_mod (a -c) b); try rewrite Zplus_0_l; auto with zarith.
  rewrite Zmod_mod; try apply Zmod_small; auto with zarith.
Qed.

(** * Greatest common divisor (gcd). *)

(** There is no unicity of the gcd; hence we define the predicate [gcd a b d]
     expressing that [d] is a gcd of [a] and [b].
     (We show later that the [gcd] is actually unique if we discard its sign.) *)

Inductive Zis_gcd (a b d:Z) : Prop :=
  Zis_gcd_intro :
  (d | a) ->
  (d | b) -> (forall x:Z, (x | a) -> (x | b) -> (x | d)) -> Zis_gcd a b d.

(** Trivial properties of [gcd] *)

Lemma Zis_gcd_sym : forall a b d:Z, Zis_gcd a b d -> Zis_gcd b a d.
Proof.
  simple induction 1; constructor; intuition.
Qed.

Lemma Zis_gcd_0 : forall a:Z, Zis_gcd a 0 a.
Proof.
  constructor; auto with zarith.
Qed.

Lemma Zis_gcd_1 : forall a, Zis_gcd a 1 1.
Proof.
  constructor; auto with zarith.
Qed.

Lemma Zis_gcd_refl : forall a, Zis_gcd a a a.
Proof.
  constructor; auto with zarith.
Qed.

Lemma Zis_gcd_minus : forall a b d:Z, Zis_gcd a (- b) d -> Zis_gcd b a d.
Proof.
  simple induction 1; constructor; intuition.
Qed.

Lemma Zis_gcd_opp : forall a b d:Z, Zis_gcd a b d -> Zis_gcd b a (- d).
Proof.
  simple induction 1; constructor; intuition.
Qed.

Lemma Zis_gcd_0_abs : forall a:Z, Zis_gcd 0 a (Zabs a).
Proof.
  intros a.
  apply Zabs_ind.
  intros; apply Zis_gcd_sym; apply Zis_gcd_0; auto.
  intros; apply Zis_gcd_opp; apply Zis_gcd_0; auto.
Qed.

Hint Resolve Zis_gcd_sym Zis_gcd_0 Zis_gcd_minus Zis_gcd_opp: zarith.

Theorem Zis_gcd_unique: forall a b c d : Z,
 Zis_gcd a b c -> Zis_gcd a b d ->  c = d \/ c = (- d).
Proof.
intros a b c d H1 H2.
inversion_clear H1 as [Hc1 Hc2 Hc3].
inversion_clear H2 as [Hd1 Hd2 Hd3].
assert (H3: Zdivide c d); auto.
assert (H4: Zdivide d c); auto.
apply Zdivide_antisym; auto.
Qed.


(** * Extended Euclid algorithm. *)

(** Euclid's algorithm to compute the [gcd] mainly relies on
    the following property. *)

Lemma Zis_gcd_for_euclid :
  forall a b d q:Z, Zis_gcd b (a - q * b) d -> Zis_gcd a b d.
Proof.
  simple induction 1; constructor; intuition.
  replace a with (a - q * b + q * b). auto with zarith. ring.
Qed.

Lemma Zis_gcd_for_euclid2 :
  forall b d q r:Z, Zis_gcd r b d -> Zis_gcd b (b * q + r) d.
Proof.
  simple induction 1; constructor; intuition.
  apply H2; auto.
  replace r with (b * q + r - b * q). auto with zarith. ring.
Qed.

(** We implement the extended version of Euclid's algorithm,
    i.e. the one computing Bezout's coefficients as it computes
    the [gcd]. We follow the algorithm given in Knuth's
    "Art of Computer Programming", vol 2, page 325. *)

Section extended_euclid_algorithm.

  Variables a b : Z.

  (** The specification of Euclid's algorithm is the existence of
      [u], [v] and [d] such that [ua+vb=d] and [(gcd a b d)]. *)

  Inductive Euclid : Set :=
    Euclid_intro :
    forall u v d:Z, u * a + v * b = d -> Zis_gcd a b d -> Euclid.

  (** The recursive part of Euclid's algorithm uses well-founded
      recursion of non-negative integers. It maintains 6 integers
      [u1,u2,u3,v1,v2,v3] such that the following invariant holds:
      [u1*a+u2*b=u3] and [v1*a+v2*b=v3] and [gcd(u2,v3)=gcd(a,b)].
      *)

  Lemma euclid_rec :
    forall v3:Z,
      0 <= v3 ->
      forall u1 u2 u3 v1 v2:Z,
	u1 * a + u2 * b = u3 ->
	v1 * a + v2 * b = v3 ->
	(forall d:Z, Zis_gcd u3 v3 d -> Zis_gcd a b d) -> Euclid.
  Proof.
    intros v3 Hv3; generalize Hv3; pattern v3 in |- *.
    apply Zlt_0_rec.
    clear v3 Hv3; intros.
    elim (Z_zerop x); intro.
    apply Euclid_intro with (u := u1) (v := u2) (d := u3).
    assumption.
    apply H3.
    rewrite a0; auto with zarith.
    set (q := u3 / x) in *.
    assert (Hq : 0 <= u3 - q * x < x).
    replace (u3 - q * x) with (u3 mod x).
    apply Z_mod_lt; omega.
    assert (xpos : x > 0). omega.
    generalize (Z_div_mod_eq u3 x xpos).
    unfold q in |- *.
    intro eq; pattern u3 at 2 in |- *; rewrite eq; ring.
    apply (H (u3 - q * x) Hq (proj1 Hq) v1 v2 x (u1 - q * v1) (u2 - q * v2)).
    tauto.
    replace ((u1 - q * v1) * a + (u2 - q * v2) * b) with
      (u1 * a + u2 * b - q * (v1 * a + v2 * b)).
    rewrite H1; rewrite H2; trivial.
    ring.
    intros; apply H3.
    apply Zis_gcd_for_euclid with q; assumption.
    assumption.
  Qed.

  (** We get Euclid's algorithm by applying [euclid_rec] on
      [1,0,a,0,1,b] when [b>=0] and [1,0,a,0,-1,-b] when [b<0]. *)

  Lemma euclid : Euclid.
  Proof.
    case (Z_le_gt_dec 0 b); intro.
    intros;
      apply euclid_rec with
	(u1 := 1) (u2 := 0) (u3 := a) (v1 := 0) (v2 := 1) (v3 := b);
	auto with zarith; ring.
    intros;
      apply euclid_rec with
	(u1 := 1) (u2 := 0) (u3 := a) (v1 := 0) (v2 := -1) (v3 := - b);
	auto with zarith; try ring.
  Qed.

End extended_euclid_algorithm.

Theorem Zis_gcd_uniqueness_apart_sign :
  forall a b d d':Z, Zis_gcd a b d -> Zis_gcd a b d' -> d = d' \/ d = - d'.
Proof.
  simple induction 1.
  intros H1 H2 H3; simple induction 1; intros.
  generalize (H3 d' H4 H5); intro Hd'd.
  generalize (H6 d H1 H2); intro Hdd'.
  exact (Zdivide_antisym d d' Hdd' Hd'd).
Qed.

(** * Bezout's coefficients *)

Inductive Bezout (a b d:Z) : Prop :=
  Bezout_intro : forall u v:Z, u * a + v * b = d -> Bezout a b d.

(** Existence of Bezout's coefficients for the [gcd] of [a] and [b] *)

Lemma Zis_gcd_bezout : forall a b d:Z, Zis_gcd a b d -> Bezout a b d.
Proof.
  intros a b d Hgcd.
  elim (euclid a b); intros u v d0 e g.
  generalize (Zis_gcd_uniqueness_apart_sign a b d d0 Hgcd g).
  intro H; elim H; clear H; intros.
  apply Bezout_intro with u v.
  rewrite H; assumption.
  apply Bezout_intro with (- u) (- v).
  rewrite H; rewrite <- e; ring.
Qed.

(** gcd of [ca] and [cb] is [c gcd(a,b)]. *)

Lemma Zis_gcd_mult :
  forall a b c d:Z, Zis_gcd a b d -> Zis_gcd (c * a) (c * b) (c * d).
Proof.
  intros a b c d; simple induction 1; constructor; intuition.
  elim (Zis_gcd_bezout a b d H). intros.
  elim H3; intros.
  elim H4; intros.
  apply Zdivide_intro with (u * q + v * q0).
  rewrite <- H5.
  replace (c * (u * a + v * b)) with (u * (c * a) + v * (c * b)).
  rewrite H6; rewrite H7; ring.
  ring.
Qed.


(** * Relative primality *)

Definition rel_prime (a b:Z) : Prop := Zis_gcd a b 1.

(** Bezout's theorem: [a] and [b] are relatively prime if and
    only if there exist [u] and [v] such that [ua+vb = 1]. *)

Lemma rel_prime_bezout : forall a b:Z, rel_prime a b -> Bezout a b 1.
Proof.
  intros a b; exact (Zis_gcd_bezout a b 1).
Qed.

Lemma bezout_rel_prime : forall a b:Z, Bezout a b 1 -> rel_prime a b.
Proof.
  simple induction 1; constructor; auto with zarith.
  intros. rewrite <- H0; auto with zarith.
Qed.

(** Gauss's theorem: if [a] divides [bc] and if [a] and [b] are
    relatively prime, then [a] divides [c]. *)

Theorem Gauss : forall a b c:Z, (a | b * c) -> rel_prime a b -> (a | c).
Proof.
  intros. elim (rel_prime_bezout a b H0); intros.
  replace c with (c * 1); [ idtac | ring ].
  rewrite <- H1.
  replace (c * (u * a + v * b)) with (c * u * a + v * (b * c));
    [ eauto with zarith | ring ].
Qed.

(** If [a] is relatively prime to [b] and [c], then it is to [bc] *)

Lemma rel_prime_mult :
  forall a b c:Z, rel_prime a b -> rel_prime a c -> rel_prime a (b * c).
Proof.
  intros a b c Hb Hc.
  elim (rel_prime_bezout a b Hb); intros.
  elim (rel_prime_bezout a c Hc); intros.
  apply bezout_rel_prime.
  apply Bezout_intro with
    (u := u * u0 * a + v0 * c * u + u0 * v * b) (v := v * v0).
  rewrite <- H.
  replace (u * a + v * b) with ((u * a + v * b) * 1); [ idtac | ring ].
  rewrite <- H0.
  ring.
Qed.

Lemma rel_prime_cross_prod :
  forall a b c d:Z,
    rel_prime a b ->
    rel_prime c d -> b > 0 -> d > 0 -> a * d = b * c -> a = c /\ b = d.
Proof.
  intros a b c d; intros.
  elim (Zdivide_antisym b d).
  split; auto with zarith.
  rewrite H4 in H3.
  rewrite Zmult_comm in H3.
  apply Zmult_reg_l with d; auto with zarith.
  intros; omega.
  apply Gauss with a.
  rewrite H3.
  auto with zarith.
  red in |- *; auto with zarith.
  apply Gauss with c.
  rewrite Zmult_comm.
  rewrite <- H3.
  auto with zarith.
  red in |- *; auto with zarith.
Qed.

(** After factorization by a gcd, the original numbers are relatively prime. *)

Lemma Zis_gcd_rel_prime :
  forall a b g:Z,
    b > 0 -> g >= 0 -> Zis_gcd a b g -> rel_prime (a / g) (b / g).
Proof.
  intros a b g; intros.
  assert (g <> 0).
  intro.
  elim H1; intros.
  elim H4; intros.
  rewrite H2 in H6; subst b; omega.
  unfold rel_prime in |- *.
  destruct H1.
  destruct H1 as (a',H1).
  destruct H3 as (b',H3).
  replace (a/g) with a';
    [|rewrite H1; rewrite Z_div_mult; auto with zarith].
  replace (b/g) with b';
    [|rewrite H3; rewrite Z_div_mult; auto with zarith].
  constructor.
  exists a'; auto with zarith.
  exists b'; auto with zarith.
  intros x (xa,H5) (xb,H6).
  destruct (H4 (x*g)).
  exists xa; rewrite Zmult_assoc; rewrite <- H5; auto.
  exists xb; rewrite Zmult_assoc; rewrite <- H6; auto.
  replace g with (1*g) in H7; auto with zarith.
  do 2 rewrite Zmult_assoc in H7.
  generalize (Zmult_reg_r _ _ _ H2 H7); clear H7; intros.
  rewrite Zmult_1_r in H7.
  exists q; auto with zarith.
Qed.

Theorem rel_prime_sym: forall a b, rel_prime a b -> rel_prime b a.
Proof.
  intros a b H; auto with zarith.
  red; apply Zis_gcd_sym; auto with zarith.
Qed.

Theorem rel_prime_div: forall p q r,
 rel_prime p q -> (r | p) -> rel_prime r q.
Proof.
  intros p q r H (u, H1); subst.
  inversion_clear H as [H1 H2 H3].
  red; apply Zis_gcd_intro; try apply Zone_divide.
  intros x H4 H5; apply H3; auto.
  apply Zdivide_mult_r; auto.
Qed.

Theorem rel_prime_1: forall n, rel_prime 1 n.
Proof.
  intros n; red; apply Zis_gcd_intro; auto.
  exists 1; auto with zarith.
  exists n; auto with zarith.
Qed.

Theorem not_rel_prime_0: forall n, 1 < n -> ~ rel_prime 0 n.
Proof.
  intros n H H1; absurd (n = 1 \/ n = -1).
  intros [H2 | H2]; subst; contradict H; auto with zarith.
  case (Zis_gcd_unique  0 n n 1); auto.
  apply Zis_gcd_intro; auto.
  exists 0; auto with zarith.
  exists 1; auto with zarith.
Qed.

Theorem rel_prime_mod: forall p q, 0 < q ->
 rel_prime p q -> rel_prime (p mod q) q.
Proof.
  intros p q H H0.
  assert (H1: Bezout p q 1).
  apply rel_prime_bezout; auto.
  inversion_clear H1 as [q1 r1 H2].
  apply bezout_rel_prime.
  apply Bezout_intro with q1  (r1 + q1 * (p / q)).
  rewrite <- H2.
  pattern p at 3; rewrite (Z_div_mod_eq p q); try ring; auto with zarith.
Qed.

Theorem rel_prime_mod_rev: forall p q, 0 < q ->
 rel_prime (p mod q) q -> rel_prime p q.
Proof.
  intros p q H H0.
  rewrite (Z_div_mod_eq p q); auto with zarith; red.
  apply Zis_gcd_sym; apply Zis_gcd_for_euclid2; auto with zarith.
Qed.

Theorem Zrel_prime_neq_mod_0: forall a b, 1 < b -> rel_prime a b -> a mod b <> 0.
Proof.
  intros a b H H1 H2.
  case (not_rel_prime_0 _ H).
  rewrite <- H2.
  apply rel_prime_mod; auto with zarith.
Qed.

(** * Primality *)

Inductive prime (p:Z) : Prop :=
  prime_intro :
    1 < p -> (forall n:Z, 1 <= n < p -> rel_prime n p) -> prime p.

(** The sole divisors of a prime number [p] are [-1], [1], [p] and [-p]. *)

Lemma prime_divisors :
  forall p:Z,
    prime p -> forall a:Z, (a | p) -> a = -1 \/ a = 1 \/ a = p \/ a = - p.
Proof.
  simple induction 1; intros.
  assert
    (a = - p \/ - p < a < -1 \/ a = -1 \/ a = 0 \/ a = 1 \/ 1 < a < p \/ a = p).
  assert (Zabs a <= Zabs p). apply Zdivide_bounds; [ assumption | omega ].
  generalize H3.
  pattern (Zabs a) in |- *; apply Zabs_ind; pattern (Zabs p) in |- *;
    apply Zabs_ind; intros; omega.
  intuition idtac.
  (* -p < a < -1 *)
  absurd (rel_prime (- a) p); intuition.
  inversion H3.
  assert (- a | - a); auto with zarith.
  assert (- a | p); auto with zarith.
  generalize (H8 (- a) H9 H10); intuition idtac.
  generalize (Zdivide_1 (- a) H11); intuition.
  (* a = 0 *)
  inversion H2. subst a; omega.
  (* 1 < a < p *)
  absurd (rel_prime a p); intuition.
  inversion H3.
  assert (a | a); auto with zarith.
  assert (a | p); auto with zarith.
  generalize (H8 a H9 H10); intuition idtac.
  generalize (Zdivide_1 a H11); intuition.
Qed.

(** A prime number is relatively prime with any number it does not divide *)

Lemma prime_rel_prime :
  forall p:Z, prime p -> forall a:Z, ~ (p | a) -> rel_prime p a.
Proof.
  simple induction 1; intros.
  constructor; intuition.
  elim (prime_divisors p H x H3); intuition; subst; auto with zarith.
  absurd (p | a); auto with zarith.
  absurd (p | a); intuition.
Qed.

Hint Resolve prime_rel_prime: zarith.

(** As a consequence, a prime number is relatively prime with smaller numbers *)

Theorem rel_prime_le_prime:
 forall a p, prime p -> 1 <=  a < p -> rel_prime a p.
Proof.
  intros a p Hp [H1 H2].
  apply rel_prime_sym; apply prime_rel_prime; auto.
  intros [q Hq]; subst a.
  case (Zle_or_lt q 0); intros Hl.
  absurd (q * p <= 0 * p); auto with zarith.
  absurd (1 * p <= q * p); auto with zarith.
Qed.


(** If a prime [p] divides [ab] then it divides either [a] or [b] *)

Lemma prime_mult :
  forall p:Z, prime p -> forall a b:Z, (p | a * b) -> (p | a) \/ (p | b).
Proof.
  intro p; simple induction 1; intros.
  case (Zdivide_dec p a); intuition.
  right; apply Gauss with a; auto with zarith.
Qed.

Lemma not_prime_0: ~ prime 0.
Proof.
  intros H1; case (prime_divisors _ H1 2); auto with zarith.
Qed.

Lemma not_prime_1: ~ prime 1.
Proof.
  intros H1; absurd (1 < 1); auto with zarith.
  inversion H1; auto.
Qed.

Lemma prime_2: prime 2.
Proof.
  apply prime_intro; auto with zarith.
  intros n [H1 H2]; case Zle_lt_or_eq with ( 1 := H1 ); auto with zarith;
   clear H1; intros H1.
  contradict H2; auto with zarith.
  subst n; red; auto with zarith.
  apply Zis_gcd_intro; auto with zarith.
Qed.

Theorem prime_3: prime 3.
Proof.
  apply prime_intro; auto with zarith.
  intros n [H1 H2]; case Zle_lt_or_eq with ( 1 := H1 ); auto with zarith;
   clear H1; intros H1.
  case (Zle_lt_or_eq 2 n); auto with zarith; clear H1; intros H1.
  contradict H2; auto with zarith.
  subst n; red; auto with zarith.
  apply Zis_gcd_intro; auto with zarith.
  intros x [q1 Hq1] [q2 Hq2].
  exists (q2 - q1).
  apply trans_equal with (3 - 2); auto with zarith.
  rewrite Hq1; rewrite Hq2; ring.
  subst n; red; auto with zarith.
  apply Zis_gcd_intro; auto with zarith.
Qed.

Theorem prime_ge_2: forall p, prime p ->  2 <= p.
Proof.
  intros p Hp; inversion Hp; auto with zarith.
Qed.

Definition prime' p := 1<p /\ (forall n, 1<n<p -> ~ (n|p)).

Theorem prime_alt:
 forall p, prime' p <-> prime p.
Proof.
  split; destruct 1; intros.
  (* prime -> prime' *)
  constructor; auto; intros.
  red; apply Zis_gcd_intro; auto with zarith; intros.
  case (Zle_lt_or_eq 0 (Zabs x)); auto with zarith; intros H6.
  case (Zle_lt_or_eq 1 (Zabs x)); auto with zarith; intros H7.
  case (Zle_lt_or_eq (Zabs x) p); auto with zarith.
  apply Zdivide_le; auto with zarith.
  apply Zdivide_Zabs_inv_l; auto.
  intros H8; case (H0 (Zabs x)); auto.
  apply Zdivide_Zabs_inv_l; auto.
  intros H8; subst p; absurd (Zabs x <= n); auto with zarith.
  apply Zdivide_le; auto with zarith.
  apply Zdivide_Zabs_inv_l; auto.
  rewrite H7; pattern (Zabs x); apply Zabs_intro; auto with zarith.
  absurd (0%Z = p); auto with zarith.
  assert (x=0) by (destruct x; simpl in *; now auto).
  subst x; elim H3; intro q; rewrite Zmult_0_r; auto.
  (* prime' -> prime *)
  split; auto; intros.
  intros H2.
  case (Zis_gcd_unique n p n 1); auto with zarith.
  apply Zis_gcd_intro; auto with zarith.
  apply H0; auto with zarith.
Qed.

Theorem square_not_prime: forall a, ~ prime (a * a).
Proof.
  intros a Ha.
  rewrite <- (Zabs_square a) in Ha.
  assert (0 <= Zabs a) by auto with zarith.
  set (b:=Zabs a) in *; clearbody b.
  rewrite <- prime_alt in Ha; destruct Ha.
  case (Zle_lt_or_eq 0 b); auto with zarith; intros Hza1; [ | subst; omega].
  case (Zle_lt_or_eq 1 b); auto with zarith; intros Hza2; [ | subst; omega].
  assert (Hza3 := Zmult_lt_compat_r 1 b b Hza1 Hza2).
  rewrite Zmult_1_l in Hza3.
  elim (H1 _ (conj Hza2 Hza3)).
  exists b; auto.
Qed.

Theorem prime_div_prime: forall p q,
 prime p -> prime q -> (p | q) -> p = q.
Proof.
  intros p q H H1 H2;
  assert (Hp: 0 < p); try apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
  assert (Hq: 0 < q); try apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
  case prime_divisors with (2 := H2); auto.
  intros H4; contradict Hp; subst; auto with zarith.
  intros [H4| [H4 | H4]]; subst; auto.
  contradict H; auto; apply not_prime_1.
  contradict Hp; auto with zarith.
Qed.


(** We could obtain a [Zgcd] function via Euclid algorithm. But we propose
  here a binary version of [Zgcd], faster and executable within Coq.

   Algorithm:

   gcd 0 b = b
   gcd a 0 = a
   gcd (2a) (2b) = 2(gcd a b)
   gcd (2a+1) (2b) = gcd (2a+1) b
   gcd (2a) (2b+1) = gcd a (2b+1)
   gcd (2a+1) (2b+1) = gcd (b-a) (2*a+1)
                    or gcd (a-b) (2*b+1), depending on whether a<b
*)

Open Scope positive_scope.

Fixpoint Pgcdn (n: nat) (a b : positive) : positive :=
  match n with
    | O => 1
    | S n =>
      match a,b with
	| xH, _ => 1
	| _, xH => 1
	| xO a, xO b => xO (Pgcdn n a b)
	| a, xO b => Pgcdn n a b
	| xO a, b => Pgcdn n a b
	| xI a', xI b' =>
          match Pcompare a' b' Eq with
	    | Eq => a
	    | Lt => Pgcdn  n (b'-a') a
	    | Gt => Pgcdn n (a'-b') b
          end
      end
  end.

Definition Pgcd (a b: positive) := Pgcdn (Psize a + Psize b)%nat a b.

Close Scope positive_scope.

Definition Zgcd (a b : Z) : Z :=
  match a,b with
    | Z0, _ => Zabs b
    | _, Z0 => Zabs a
    | Zpos a, Zpos b => Zpos (Pgcd a b)
    | Zpos a, Zneg b => Zpos (Pgcd a b)
    | Zneg a, Zpos b => Zpos (Pgcd a b)
    | Zneg a, Zneg b => Zpos (Pgcd a b)
  end.

Lemma Zgcd_is_pos : forall a b, 0 <= Zgcd a b.
Proof.
  unfold Zgcd; destruct a; destruct b; auto with zarith.
Qed.

Lemma Zis_gcd_even_odd : forall a b g, Zis_gcd (Zpos a) (Zpos (xI b)) g ->
  Zis_gcd (Zpos (xO a)) (Zpos (xI b)) g.
Proof.
  intros.
  destruct H.
  constructor; auto.
  destruct H as (e,H2); exists (2*e); auto with zarith.
  rewrite Zpos_xO; rewrite H2; ring.
  intros.
  apply H1; auto.
  rewrite Zpos_xO in H2.
  rewrite Zpos_xI in H3.
  apply Gauss with 2; auto.
  apply bezout_rel_prime.
  destruct H3 as (bb, H3).
  apply Bezout_intro with bb (-Zpos b).
  omega.
Qed.

Lemma Pgcdn_correct : forall n a b, (Psize a + Psize b<=n)%nat ->
  Zis_gcd (Zpos a) (Zpos b) (Zpos (Pgcdn n a b)).
Proof.
  intro n; pattern n; apply lt_wf_ind; clear n; intros.
  destruct n.
  simpl.
  destruct a; simpl in *; try inversion H0.
  destruct a.
  destruct b; simpl.
  case_eq (Pcompare a b Eq); intros.
  (* a = xI, b = xI, compare = Eq *)
  rewrite (Pcompare_Eq_eq _ _ H1); apply Zis_gcd_refl.
  (* a = xI, b = xI, compare = Lt *)
  apply Zis_gcd_sym.
  apply Zis_gcd_for_euclid with 1.
  apply Zis_gcd_sym.
  replace (Zpos (xI b) - 1 * Zpos (xI a)) with (Zpos(xO (b - a))).
  apply Zis_gcd_even_odd.
  apply H; auto.
  simpl in *.
  assert (Psize (b-a) <= Psize b)%nat.
  apply Psize_monotone.
  change (Zpos (b-a) < Zpos b).
  rewrite (Zpos_minus_morphism _ _ H1).
  assert (0 < Zpos a) by (compute; auto).
  omega.
  omega.
  rewrite Zpos_xO; do 2 rewrite Zpos_xI.
  rewrite Zpos_minus_morphism; auto.
  omega.
  (* a = xI, b = xI, compare = Gt *)
  apply Zis_gcd_for_euclid with 1.
  replace (Zpos (xI a) - 1 * Zpos (xI b)) with (Zpos(xO (a - b))).
  apply Zis_gcd_sym.
  apply Zis_gcd_even_odd.
  apply H; auto.
  simpl in *.
  assert (Psize (a-b) <= Psize a)%nat.
  apply Psize_monotone.
  change (Zpos (a-b) < Zpos a).
  rewrite (Zpos_minus_morphism b a).
  assert (0 < Zpos b) by (compute; auto).
  omega.
  rewrite ZC4; rewrite H1; auto.
  omega.
  rewrite Zpos_xO; do 2 rewrite Zpos_xI.
  rewrite Zpos_minus_morphism; auto.
  omega.
  rewrite ZC4; rewrite H1; auto.
  (* a = xI, b = xO *)
  apply Zis_gcd_sym.
  apply Zis_gcd_even_odd.
  apply Zis_gcd_sym.
  apply H; auto.
  simpl in *; omega.
  (* a = xI, b = xH *)
  apply Zis_gcd_1.
  destruct b; simpl.
  (* a = xO, b = xI *)
  apply Zis_gcd_even_odd.
  apply H; auto.
  simpl in *; omega.
  (* a = xO, b = xO *)
  rewrite (Zpos_xO a); rewrite (Zpos_xO b); rewrite (Zpos_xO (Pgcdn n a b)).
  apply Zis_gcd_mult.
  apply H; auto.
  simpl in *; omega.
  (* a = xO, b = xH *)
  apply Zis_gcd_1.
  (* a = xH *)
  simpl; apply Zis_gcd_sym; apply Zis_gcd_1.
Qed.

Lemma Pgcd_correct : forall a b, Zis_gcd (Zpos a) (Zpos b) (Zpos (Pgcd a b)).
Proof.
  unfold Pgcd; intros.
  apply Pgcdn_correct; auto.
Qed.

Lemma Zgcd_is_gcd : forall a b, Zis_gcd a b (Zgcd a b).
Proof.
  destruct a.
  intros.
  simpl.
  apply Zis_gcd_0_abs.
  destruct b; simpl.
  apply Zis_gcd_0.
  apply Pgcd_correct.
  apply Zis_gcd_sym.
  apply Zis_gcd_minus; simpl.
  apply Pgcd_correct.
  destruct b; simpl.
  apply Zis_gcd_minus; simpl.
  apply Zis_gcd_sym.
  apply Zis_gcd_0.
  apply Zis_gcd_minus; simpl.
  apply Zis_gcd_sym.
  apply Pgcd_correct.
  apply Zis_gcd_sym.
  apply Zis_gcd_minus; simpl.
  apply Zis_gcd_minus; simpl.
  apply Zis_gcd_sym.
  apply Pgcd_correct.
Qed.

Theorem Zgcd_spec : forall x y : Z, {z : Z | Zis_gcd x y z /\ 0 <= z}.
Proof.
  intros x y; exists (Zgcd x y).
  split; [apply Zgcd_is_gcd  | apply Zgcd_is_pos].
Qed.

Theorem Zdivide_Zgcd: forall p q r : Z,
 (p | q) -> (p | r) -> (p | Zgcd q r).
Proof.
  intros p q r H1 H2.
  assert (H3: (Zis_gcd q r (Zgcd q r))).
  apply Zgcd_is_gcd.
  inversion_clear H3; auto.
Qed.

Theorem Zis_gcd_gcd: forall a b c : Z,
 0 <= c ->  Zis_gcd a b c -> Zgcd a b = c.
Proof.
  intros a b c H1 H2.
  case (Zis_gcd_uniqueness_apart_sign a b c (Zgcd a b)); auto.
  apply Zgcd_is_gcd; auto.
  case Zle_lt_or_eq with (1 := H1); clear H1; intros H1; subst; auto.
  intros H3; subst.
  generalize (Zgcd_is_pos a b); auto with zarith.
  case (Zgcd a b); simpl; auto; intros; discriminate.
Qed.

Theorem Zgcd_inv_0_l: forall x y, Zgcd x y = 0 -> x = 0.
Proof.
  intros x y H.
  assert (F1: Zdivide 0 x).
   rewrite <- H.
   generalize (Zgcd_is_gcd x y); intros HH; inversion HH; auto.
  inversion F1 as [z H1].
  rewrite H1; ring.
Qed.

Theorem Zgcd_inv_0_r: forall x y, Zgcd x y = 0 -> y = 0.
Proof.
  intros x y H.
  assert (F1: Zdivide 0 y).
   rewrite <- H.
   generalize (Zgcd_is_gcd x y); intros HH; inversion HH; auto.
  inversion F1 as [z H1].
  rewrite H1; ring.
Qed.

Theorem Zgcd_div_swap0 : forall a b : Z,
 0 < Zgcd a b ->
 0 < b ->
 (a / Zgcd a b) * b = a * (b/Zgcd a b).
Proof.
  intros a b Hg Hb.
  assert (F := Zgcd_is_gcd a b); inversion F as [F1 F2 F3].
  pattern b at 2; rewrite (Zdivide_Zdiv_eq (Zgcd a b) b); auto.
  repeat rewrite Zmult_assoc; f_equal.
  rewrite Zmult_comm.
  rewrite <- Zdivide_Zdiv_eq; auto.
Qed.

Theorem Zgcd_div_swap : forall a b c : Z,
 0 < Zgcd a b ->
 0 < b ->
 (c * a) / Zgcd a b * b = c * a * (b/Zgcd a b).
Proof.
  intros a b c Hg Hb.
  assert (F := Zgcd_is_gcd a b); inversion F as [F1 F2 F3].
  pattern b at 2; rewrite (Zdivide_Zdiv_eq (Zgcd a b) b); auto.
  repeat rewrite Zmult_assoc; f_equal.
  rewrite Zdivide_Zdiv_eq_2; auto.
  repeat rewrite <- Zmult_assoc; f_equal.
  rewrite Zmult_comm.
  rewrite <- Zdivide_Zdiv_eq; auto.
Qed.

Lemma Zgcd_comm : forall a b, Zgcd a b = Zgcd b a.
Proof.
  intros.
  apply Zis_gcd_gcd.
  apply Zgcd_is_pos.
  apply Zis_gcd_sym.
  apply Zgcd_is_gcd.
Qed.

Lemma Zgcd_ass : forall a b c, Zgcd (Zgcd a b) c = Zgcd a (Zgcd b c).
Proof.
  intros.
  apply Zis_gcd_gcd.
  apply Zgcd_is_pos.
  destruct (Zgcd_is_gcd a b).
  destruct (Zgcd_is_gcd b c).
  destruct (Zgcd_is_gcd a (Zgcd b c)).
  constructor; eauto using Zdivide_trans.
Qed.

Lemma Zgcd_Zabs : forall a b, Zgcd (Zabs a) b = Zgcd a b.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma Zgcd_0 : forall a, Zgcd a 0 = Zabs a.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma Zgcd_1 : forall a, Zgcd a 1 = 1.
Proof.
  intros; apply Zis_gcd_gcd; auto with zarith; apply Zis_gcd_1.
Qed.
Hint Resolve Zgcd_0 Zgcd_1 : zarith.

Theorem Zgcd_1_rel_prime : forall a b,
 Zgcd a b = 1 <-> rel_prime a b.
Proof.
  unfold rel_prime; split; intro H.
  rewrite <- H; apply Zgcd_is_gcd.
  case (Zis_gcd_unique a b (Zgcd a b) 1); auto.
  apply Zgcd_is_gcd.
  intros H2; absurd (0 <= Zgcd a b); auto with zarith.
  generalize (Zgcd_is_pos a b); auto with zarith.
Qed.

Definition rel_prime_dec: forall a b,
 { rel_prime a b }+{ ~ rel_prime a b }.
Proof.
  intros a b; case (Z_eq_dec (Zgcd a b) 1); intros H1.
  left; apply -> Zgcd_1_rel_prime; auto.
  right; contradict H1; apply <- Zgcd_1_rel_prime; auto.
Defined.

Definition prime_dec_aux:
 forall p m,
  { forall n, 1 < n < m -> rel_prime n p } +
  { exists n, 1 < n < m  /\ ~ rel_prime n p }.
Proof.
  intros p m.
  case (Z_lt_dec 1 m); intros H1;
   [ | left; intros; exfalso; omega ].
  pattern m; apply natlike_rec; auto with zarith.
  left; intros; exfalso; omega.
  intros x Hx IH; destruct IH as [F|E].
  destruct (rel_prime_dec x p) as [Y|N].
  left; intros n [HH1 HH2].
  case (Zgt_succ_gt_or_eq x n); auto with zarith.
  intros HH3; subst x; auto.
  case (Z_lt_dec 1 x); intros HH1.
  right; exists x; split; auto with zarith.
  left; intros n [HHH1 HHH2]; contradict HHH1; auto with zarith.
  right; destruct E as (n,((H0,H2),H3)); exists n; auto with zarith.
Defined.

Definition prime_dec: forall p, { prime p }+{ ~ prime p }.
Proof.
  intros p; case (Z_lt_dec 1 p); intros H1.
  case (prime_dec_aux p p); intros H2.
  left; apply prime_intro; auto.
  intros n [Hn1 Hn2]; case Zle_lt_or_eq with ( 1 := Hn1 ); auto.
  intros HH; subst n.
  red; apply Zis_gcd_intro; auto with zarith.
  right; intros H3; inversion_clear H3 as [Hp1 Hp2].
  case H2; intros n [Hn1 Hn2]; case Hn2; auto with zarith.
  right; intros H3; inversion_clear H3 as [Hp1 Hp2]; case H1; auto.
Defined.

Theorem not_prime_divide:
 forall p, 1 < p -> ~ prime p -> exists n, 1 < n < p  /\ (n | p).
Proof.
  intros p Hp Hp1.
  case (prime_dec_aux p p); intros H1.
  elim Hp1; constructor; auto.
  intros n [Hn1 Hn2].
  case Zle_lt_or_eq with ( 1 := Hn1 ); auto with zarith.
  intros H2; subst n; red; apply Zis_gcd_intro; auto with zarith.
  case H1; intros n [Hn1 Hn2].
  generalize (Zgcd_is_pos n p); intros Hpos.
  case (Zle_lt_or_eq 0 (Zgcd n p)); auto with zarith; intros H3.
  case (Zle_lt_or_eq 1 (Zgcd n p)); auto with zarith; intros H4.
  exists (Zgcd n p); split; auto.
  split; auto.
  apply Zle_lt_trans with n; auto with zarith.
  generalize (Zgcd_is_gcd n p); intros tmp; inversion_clear tmp as [Hr1 Hr2 Hr3].
  case Hr1; intros q Hq.
  case (Zle_or_lt q 0); auto with zarith; intros Ht.
  absurd (n <= 0 * Zgcd n p) ; auto with zarith.
  pattern n at 1; rewrite Hq; auto with zarith.
  apply Zle_trans with (1 * Zgcd n p); auto with zarith.
  pattern n at 2; rewrite Hq; auto with zarith.
  generalize (Zgcd_is_gcd n p); intros Ht; inversion Ht; auto.
  case Hn2; red.
  rewrite H4; apply Zgcd_is_gcd.
  generalize (Zgcd_is_gcd n p); rewrite <- H3; intros tmp;
  inversion_clear tmp as [Hr1 Hr2 Hr3].
  absurd (n = 0); auto with zarith.
  case Hr1; auto with zarith.
Qed.

(** A Generalized Gcd that also computes Bezout coefficients.
   The algorithm is the same as for Zgcd. *)

Open Scope positive_scope.

Fixpoint Pggcdn (n: nat) (a b : positive) : (positive*(positive*positive)) :=
  match n with
    | O => (1,(a,b))
    | S n =>
      match a,b with
	| xH, b => (1,(1,b))
	| a, xH => (1,(a,1))
	| xO a, xO b =>
           let (g,p) := Pggcdn n a b in
           (xO g,p)
	| a, xO b =>
           let (g,p) := Pggcdn n a b in
           let (aa,bb) := p in
           (g,(aa, xO bb))
	| xO a, b =>
           let (g,p) := Pggcdn n a b in
           let (aa,bb) := p in
           (g,(xO aa, bb))
	| xI a', xI b' =>
           match Pcompare a' b' Eq with
	     | Eq => (a,(1,1))
	     | Lt =>
	        let (g,p) := Pggcdn n (b'-a') a in
	        let (ba,aa) := p in
	        (g,(aa, aa + xO ba))
	     | Gt =>
		let (g,p) := Pggcdn n (a'-b') b in
		let (ab,bb) := p in
		(g,(bb+xO ab, bb))
	   end
      end
  end.

Definition Pggcd (a b: positive) := Pggcdn (Psize a + Psize b)%nat a b.

Open Scope Z_scope.

Definition Zggcd (a b : Z) : Z*(Z*Z) :=
  match a,b with
    | Z0, _ => (Zabs b,(0, Zsgn b))
    | _, Z0 => (Zabs a,(Zsgn a, 0))
    | Zpos a, Zpos b =>
       let (g,p) := Pggcd a b in
       let (aa,bb) := p in
       (Zpos g, (Zpos aa, Zpos bb))
    | Zpos a, Zneg b =>
       let (g,p) := Pggcd a b in
       let (aa,bb) := p in
       (Zpos g, (Zpos aa, Zneg bb))
    | Zneg a, Zpos b =>
       let (g,p) := Pggcd a b in
       let (aa,bb) := p in
       (Zpos g, (Zneg aa, Zpos bb))
    | Zneg a, Zneg b =>
       let (g,p) := Pggcd a b in
       let (aa,bb) := p in
       (Zpos g, (Zneg aa, Zneg bb))
  end.


Lemma Pggcdn_gcdn : forall n a b,
  fst (Pggcdn n a b) = Pgcdn n a b.
Proof.
  induction n.
  simpl; auto.
  destruct a; destruct b; simpl; auto.
  destruct (Pcompare a b Eq); simpl; auto.
  rewrite <- IHn; destruct (Pggcdn n (b-a) (xI a)) as (g,(aa,bb)); simpl; auto.
  rewrite <- IHn; destruct (Pggcdn n (a-b) (xI b)) as (g,(aa,bb)); simpl; auto.
  rewrite <- IHn; destruct (Pggcdn n (xI a) b) as (g,(aa,bb)); simpl; auto.
  rewrite <- IHn; destruct (Pggcdn n a (xI b)) as (g,(aa,bb)); simpl; auto.
  rewrite <- IHn; destruct (Pggcdn n a b) as (g,(aa,bb)); simpl; auto.
Qed.

Lemma Pggcd_gcd : forall a b, fst (Pggcd a b) = Pgcd a b.
Proof.
  intros; exact (Pggcdn_gcdn (Psize a+Psize b)%nat a b).
Qed.

Lemma Zggcd_gcd : forall a b, fst (Zggcd a b) = Zgcd a b.
Proof.
  destruct a; destruct b; simpl; auto; rewrite <- Pggcd_gcd;
    destruct (Pggcd p p0) as (g,(aa,bb)); simpl; auto.
Qed.

Open Scope positive_scope.

Lemma Pggcdn_correct_divisors : forall n a b,
  let (g,p) := Pggcdn n a b in
  let (aa,bb):=p in
  (a=g*aa) /\ (b=g*bb).
Proof.
  induction n.
  simpl; auto.
  destruct a; destruct b; simpl; auto.
  case_eq (Pcompare a b Eq); intros.
  (* Eq *)
  rewrite Pmult_comm; simpl; auto.
  rewrite (Pcompare_Eq_eq _ _ H); auto.
  (* Lt *)
  generalize (IHn (b-a) (xI a)); destruct (Pggcdn n (b-a) (xI a)) as (g,(ba,aa)); simpl.
  intros (H0,H1); split; auto.
  rewrite Pmult_plus_distr_l.
  rewrite Pmult_xO_permute_r.
  rewrite <- H1; rewrite <- H0.
  simpl; f_equal; symmetry.
  apply Pplus_minus; auto.
  rewrite ZC4; rewrite H; auto.
  (* Gt *)
  generalize (IHn (a-b) (xI b)); destruct (Pggcdn n (a-b) (xI b)) as (g,(ab,bb)); simpl.
  intros (H0,H1); split; auto.
  rewrite Pmult_plus_distr_l.
  rewrite Pmult_xO_permute_r.
  rewrite <- H1; rewrite <- H0.
  simpl; f_equal; symmetry.
  apply Pplus_minus; auto.
  (* Then... *)
  generalize (IHn (xI a) b); destruct (Pggcdn n (xI a) b) as (g,(ab,bb)); simpl.
  intros (H0,H1); split; auto.
  rewrite Pmult_xO_permute_r; rewrite H1; auto.
  generalize (IHn a (xI b)); destruct (Pggcdn n a (xI b)) as (g,(ab,bb)); simpl.
  intros (H0,H1); split; auto.
  rewrite Pmult_xO_permute_r; rewrite H0; auto.
  generalize (IHn a b); destruct (Pggcdn n a b) as (g,(ab,bb)); simpl.
  intros (H0,H1); split; subst; auto.
Qed.

Lemma Pggcd_correct_divisors : forall a b,
  let (g,p) := Pggcd a b in
  let (aa,bb):=p in
  (a=g*aa) /\ (b=g*bb).
Proof.
  intros a b; exact (Pggcdn_correct_divisors (Psize a + Psize b)%nat a b).
Qed.

Close Scope positive_scope.

Lemma Zggcd_correct_divisors : forall a b,
  let (g,p) := Zggcd a b in
  let (aa,bb):=p in
  (a=g*aa) /\ (b=g*bb).
Proof.
  destruct a; destruct b; simpl; auto; try solve [rewrite Pmult_comm; simpl; auto];
    generalize (Pggcd_correct_divisors p p0); destruct (Pggcd p p0) as (g,(aa,bb));
      destruct 1; subst; auto.
Qed.

Theorem Zggcd_opp: forall x y,
  Zggcd (-x) y = let (p1,p) := Zggcd x y in
                 let (p2,p3) := p in
                 (p1,(-p2,p3)).
Proof.
intros [|x|x] [|y|y]; unfold Zggcd, Zopp; auto.
case Pggcd; intros p1 (p2, p3); auto.
case Pggcd; intros p1 (p2, p3); auto.
case Pggcd; intros p1 (p2, p3); auto.
case Pggcd; intros p1 (p2, p3); auto.
Qed.
