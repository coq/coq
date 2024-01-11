(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZArith_base.
Require Import ZArithRing.
Require Import Zcomplements.
Require Import Zdiv.
Require Import Wf_nat.

(** For compatibility reasons, this Open Scope isn't local as it should *)

Open Scope Z_scope.

Local Ltac Tauto.intuition_solver ::= auto with zarith.

(** This file contains some notions of number theory upon Z numbers:
     - a divisibility predicate [Z.divide]
     - a gcd predicate [gcd]
     - Euclid algorithm [extgcd]
     - a relatively prime predicate [rel_prime]
     - a prime predicate [prime]
     - properties of the efficient [Z.gcd] function
*)

(** The former specialized inductive predicate [Z.divide] is now
    a generic existential predicate. *)

(** Its former constructor is now a pseudo-constructor. *)

Definition Zdivide_intro a b q (H:b=q*a) : Z.divide a b := ex_intro _ q H.

(** Results concerning divisibility*)

Notation Zone_divide := Z.divide_1_l (only parsing).
Notation Zdivide_0 := Z.divide_0_r (only parsing).
Notation Zmult_divide_compat_l := Z.mul_divide_mono_l (only parsing).
Notation Zmult_divide_compat_r := Z.mul_divide_mono_r (only parsing).
Notation Zdivide_plus_r := Z.divide_add_r (only parsing).
Notation Zdivide_minus_l := Z.divide_sub_r (only parsing).
Notation Zdivide_mult_l := Z.divide_mul_l (only parsing).
Notation Zdivide_mult_r := Z.divide_mul_r (only parsing).
Notation Zdivide_factor_r := Z.divide_factor_l (only parsing).
Notation Zdivide_factor_l := Z.divide_factor_r (only parsing).

Lemma Zdivide_opp_r a b : (a | b) -> (a | - b).
Proof. apply Z.divide_opp_r. Qed.

Lemma Zdivide_opp_r_rev a b : (a | - b) -> (a | b).
Proof. apply Z.divide_opp_r. Qed.

Lemma Zdivide_opp_l a b : (a | b) -> (- a | b).
Proof. apply Z.divide_opp_l. Qed.

Lemma Zdivide_opp_l_rev a b : (- a | b) -> (a | b).
Proof. apply Z.divide_opp_l. Qed.

Theorem Zdivide_Zabs_l a b : (Z.abs a | b) -> (a | b).
Proof. apply Z.divide_abs_l. Qed.

Theorem Zdivide_Zabs_inv_l a b : (a | b) -> (Z.abs a | b).
Proof. apply Z.divide_abs_l. Qed.

#[global]
Hint Resolve Z.divide_refl Z.divide_1_l Z.divide_0_r: zarith.
#[global]
Hint Resolve Z.mul_divide_mono_l Z.mul_divide_mono_r: zarith.
#[global]
Hint Resolve Z.divide_add_r Zdivide_opp_r Zdivide_opp_r_rev Zdivide_opp_l
  Zdivide_opp_l_rev Z.divide_sub_r Z.divide_mul_l Z.divide_mul_r
  Z.divide_factor_l Z.divide_factor_r: zarith.

(** Auxiliary result. *)

Lemma Zmult_one x y : x >= 0 -> x * y = 1 -> x = 1.
Proof.
 Z.swap_greater. apply Z.eq_mul_1_nonneg.
Qed.

(** Only [1] and [-1] divide [1]. *)

Notation Zdivide_1 := Z.divide_1_r (only parsing).

(** If [a] divides [b] and [b<>0] then [|a| <= |b|]. *)

Lemma Zdivide_bounds a b : (a | b) -> b <> 0 -> Z.abs a <= Z.abs b.
Proof.
 intros H Hb.
 rewrite <- Z.divide_abs_l, <- Z.divide_abs_r in H.
 apply Z.abs_pos in Hb.
 now apply Z.divide_pos_le.
Qed.

(** [Z.divide] can be expressed using [Z.modulo]. *)

Lemma Zmod_divide : forall a b, b<>0 -> a mod b = 0 -> (b | a).
Proof.
 apply Z.mod_divide.
Qed.

Lemma Zdivide_mod : forall a b, (b | a) -> a mod b = 0.
Proof.
 intros a b (c,->); apply Z_mod_mult.
Qed.

(** [Z.divide] is hence decidable *)

Lemma Zdivide_dec a b : {(a | b)} + {~ (a | b)}.
Proof.
 destruct (Z.eq_dec a 0) as [Ha|Ha].
 - destruct (Z.eq_dec b 0) as [Hb|Hb].
   + left; subst; apply Z.divide_0_r.
   + right. subst. contradict Hb. now apply Z.divide_0_l.
 - destruct (Z.eq_dec (b mod a) 0).
   + left. now apply Z.mod_divide.
   + right. now rewrite <- Z.mod_divide.
Defined.

Lemma Z_lt_neq {x y: Z} : x < y -> y <> x.
Proof. auto using Z.lt_neq, Z.neq_sym. Qed.

Theorem Zdivide_Zdiv_eq a b : 0 < a -> (a | b) ->  b = a * (b / a).
Proof.
 intros Ha H.
 rewrite (Z.div_mod b a) at 1.
 + rewrite Zdivide_mod; auto with zarith.
 + auto using Z_lt_neq.
Qed.

Theorem Zdivide_Zdiv_eq_2 a b c :
 0 < a -> (a | b) -> (c * b) / a = c * (b / a).
Proof.
 intros. apply Z.divide_div_mul_exact.
 + now apply Z_lt_neq.
 + auto with zarith.
Qed.

Theorem Zdivide_le: forall a b : Z,
 0 <= a -> 0 < b -> (a | b) ->  a <= b.
Proof.
 intros. now apply Z.divide_pos_le.
Qed.

Theorem Zdivide_Zdiv_lt_pos a b :
 1 < a -> 0 < b -> (a | b) ->  0 < b / a < b .
Proof.
  intros H1 H2 H3.
  assert (0 < a) by (now transitivity 1).
  split.
  + apply Z.mul_pos_cancel_l with a; auto.
    rewrite <- Zdivide_Zdiv_eq; auto.
  + now apply Z.div_lt.
Qed.

Lemma Zmod_div_mod n m a:
 0 < n -> 0 < m -> (n | m) -> a mod n = (a mod m) mod n.
Proof with auto using Z_lt_neq.
  intros H1 H2 (p,Hp).
  rewrite (Z.div_mod a m) at 1...
  rewrite Hp at 1.
  rewrite Z.mul_shuffle0, Z.add_comm, Z.mod_add...
Qed.

Lemma Zmod_divide_minus a b c:
 0 < b -> a mod b = c -> (b | a - c).
Proof with auto using Z_lt_neq.
  intros H H1. apply Z.mod_divide...
  rewrite Zminus_mod.
  rewrite H1. rewrite <- (Z.mod_small c b) at 1.
  - rewrite Z.sub_diag, Z.mod_0_l...
  - subst. now apply Z.mod_pos_bound.
Qed.

Lemma Zdivide_mod_minus a b c:
 0 <= c < b -> (b | a - c) -> a mod b = c.
Proof.
  intros (H1, H2) H3.
  assert (0 < b) by Z.order.
  assert (b <> 0) by now apply Z_lt_neq.
  replace a with ((a - c) + c) by ring.
  rewrite Z.add_mod; auto.
  rewrite (Zdivide_mod (a-c) b); try rewrite Z.add_0_l; auto.
  rewrite Z.mod_mod; try apply Zmod_small; auto.
Qed.

(** * Greatest common divisor (gcd). *)

(** There is no unicity of the gcd; hence we define the predicate
    [Zis_gcd a b g] expressing that [g] is a gcd of [a] and [b].
    (We show later that the [gcd] is actually unique if we discard its sign.) *)

Inductive Zis_gcd (a b g:Z) : Prop :=
 Zis_gcd_intro :
  (g | a) ->
  (g | b) ->
  (forall x, (x | a) -> (x | b) -> (x | g)) ->
  Zis_gcd a b g.

Lemma Zgcd_is_gcd : forall a b, Zis_gcd a b (Z.gcd a b).
Proof.
 constructor.
 - apply Z.gcd_divide_l.
 - apply Z.gcd_divide_r.
 - apply Z.gcd_greatest.
Qed.

(** Trivial properties of [gcd] *)

Lemma Zis_gcd_sym : forall a b d, Zis_gcd a b d -> Zis_gcd b a d.
Proof.
  induction 1; constructor; intuition.
Qed.

Lemma Zis_gcd_0 : forall a, Zis_gcd a 0 a.
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

Lemma Zis_gcd_minus : forall a b d, Zis_gcd a (- b) d -> Zis_gcd b a d.
Proof.
  induction 1; constructor; intuition.
Qed.

Lemma Zis_gcd_opp : forall a b d, Zis_gcd a b d -> Zis_gcd b a (- d).
Proof.
  induction 1; constructor; intuition.
Qed.

Lemma Zis_gcd_0_abs a : Zis_gcd 0 a (Z.abs a).
Proof.
  apply Zabs_ind.
  - intros; apply Zis_gcd_sym; apply Zis_gcd_0; auto.
  - intros; apply Zis_gcd_opp; apply Zis_gcd_0; auto.
Qed.

#[global]
Hint Resolve Zis_gcd_sym Zis_gcd_0 Zis_gcd_minus Zis_gcd_opp: zarith.

Theorem Zis_gcd_unique: forall a b c d : Z,
 Zis_gcd a b c -> Zis_gcd a b d ->  c = d \/ c = (- d).
Proof.
intros a b c d [Hc1 Hc2 Hc3] [Hd1 Hd2 Hd3].
assert (c|d) by auto.
assert (d|c) by auto.
apply Z.divide_antisym; auto.
Qed.


(** * Extended Euclid algorithm. *)

Lemma deprecated_Zis_gcd_for_euclid :
  forall a b d q:Z, Zis_gcd b (a - q * b) d -> Zis_gcd a b d.
Proof.
  intros a b d q; simple induction 1; constructor; intuition.
  replace a with (a - q * b + q * b).
  - auto with zarith.
  - ring.
Qed.
#[deprecated(since="8.17")]
Notation Zis_gcd_for_euclid := deprecated_Zis_gcd_for_euclid (only parsing).

(* this lemma is still used below and in Zgcd_alt *)
Lemma Zis_gcd_for_euclid2 :
  forall b d q r:Z, Zis_gcd r b d -> Zis_gcd b (b * q + r) d.
Proof.
  intros b d q r; destruct 1 as [? ? H]; constructor; intuition.
  apply H; auto.
  replace r with (b * q + r - b * q).
  - auto with zarith.
  - ring.
Qed.

(** We implement the extended version of Euclid's algorithm,
    i.e. the one computing Bezout's coefficients as it computes
    the [gcd]. We follow the algorithm given in Knuth's
    "Art of Computer Programming", vol 2, page 325. *)

Section extended_euclid_algorithm.

  Variables a b : Z.

  Local Lemma extgcd_rec_helper r1 r2 q :
    Z.gcd r1 r2 = Z.gcd a b -> Z.gcd (r2 - q * r1) r1 = Z.gcd a b.
  Proof.
    intros H; rewrite <-H, Z.gcd_comm.
    rewrite <-(Z.gcd_add_mult_diag_r r1 r2 (-q)). f_equal; ring.
  Qed.

  Let f := S(S(Z.to_nat(Z.log2_up(Z.log2_up(Z.abs(a*b)))))). (* log2(fuel) *)

  Local Definition extgcd_rec : forall r1 u1 v1 r2 u2 v2,
    (True -> 0 <= r1 /\ 0 <= r2 /\ r1 = u1 * a + v1 * b /\ r2 = u2 * a + v2 * b /\
        Z.gcd r1 r2 = Z.gcd a b)
     -> { '(u, v, d) | True -> u * a + v * b = d /\ d = Z.gcd a b}.
  Proof.
    refine (Fix (Acc_intro_generator f (Z.lt_wf 0)) _ (fun r1 rec u1 v1  r2 u2 v2 H =>
      if Z.eq_dec r1 0
      then exist (fun '(u, v, d) => _) (u2, v2, r2) (fun _ => _)
      else let q := r2 / r1 in
           rec (r2 - q * r1) _ (u2 - q * u1) (v2 - q * v1) r1 u1 v1 (fun _ => _))).
    all : abstract (intuition (solve
      [ subst; rewrite ?Z.gcd_0_l_nonneg in *; auto using extgcd_rec_helper; ring
      | subst q; rewrite <-Zmod_eq_full by trivial;
        apply Z.mod_pos_bound, Z.le_neq; intuition congruence ])).
  Defined.

  Definition extgcd : Z*Z*Z.
  Proof.
    refine (proj1_sig (extgcd_rec (Z.abs a) (Z.sgn a) 0 (Z.abs b) 0 (Z.sgn b) _)).
    abstract (intuition (trivial using Z.abs_nonneg;
      rewrite ?Z.gcd_abs_r, ?Z.gcd_abs_l, <-?Z.sgn_abs; ring)).
  Defined.

  Lemma extgcd_correct [u v d] : extgcd = (u, v, d) -> u * a + v * b = d /\ d = Z.gcd a b.
  Proof. cbv [extgcd proj1_sig]. case extgcd_rec as (([],?),?). intuition congruence. Qed.

  Inductive deprecated_Euclid : Set :=
    deprecated_Euclid_intro :
    forall u v d:Z, u * a + v * b = d -> Zis_gcd a b d -> deprecated_Euclid.

  Lemma deprecated_euclid : deprecated_Euclid.
  Proof. case extgcd as [[]?] eqn:H; case (extgcd_correct H); esplit; subst; eauto using Zgcd_is_gcd. Qed.

  Lemma deprecated_euclid_rec :
    forall v3:Z,
      0 <= v3 ->
      forall u1 u2 u3 v1 v2:Z,
       u1 * a + u2 * b = u3 ->
       v1 * a + v2 * b = v3 ->
       (forall d:Z, Zis_gcd u3 v3 d -> Zis_gcd a b d) -> deprecated_Euclid.
  Proof. intros; apply deprecated_euclid. Qed.

End extended_euclid_algorithm.

#[deprecated(since="8.17", note="Use Coq.ZArith.Znumtheory.extgcd")]
Notation Euclid := deprecated_Euclid (only parsing).
#[deprecated(since="8.17", note="Use Coq.ZArith.Znumtheory.extgcd")]
Notation Euclid_intro := deprecated_Euclid_intro (only parsing).
#[deprecated(since="8.17", note="Use Coq.ZArith.Znumtheory.extgcd")]
Notation euclid := deprecated_euclid (only parsing).
#[deprecated(since="8.17", note="Use Coq.ZArith.Znumtheory.extgcd")]
Notation euclid_rec := deprecated_euclid_rec (only parsing).

Theorem Zis_gcd_uniqueness_apart_sign :
  forall a b d d':Z, Zis_gcd a b d -> Zis_gcd a b d' -> d = d' \/ d = - d'.
Proof.
  intros a b d d'; simple induction 1.
  intros H1 H2 H3; destruct 1 as [H4 H5 H6].
  generalize (H3 d' H4 H5); intro Hd'd.
  generalize (H6 d H1 H2); intro Hdd'.
  exact (Z.divide_antisym d d' Hdd' Hd'd).
Qed.

(** * Bezout's coefficients *)

Inductive Bezout (a b d:Z) : Prop :=
  Bezout_intro : forall u v:Z, u * a + v * b = d -> Bezout a b d.

(** Existence of Bezout's coefficients for the [gcd] of [a] and [b] *)

Lemma Zis_gcd_bezout : forall a b d:Z, Zis_gcd a b d -> Bezout a b d.
Proof.
  intros a b d Hgcd.
  case (extgcd a b) as [[u v] g] eqn:E, (extgcd_correct _ _ E) as [G ?Hg].
  destruct (Zis_gcd_uniqueness_apart_sign a b d g Hgcd ltac:(rewrite Hg; apply Zgcd_is_gcd));
    subst; (apply Bezout_intro with u v + apply Bezout_intro with (- u) (- v)); ring.
Qed.

(** gcd of [ca] and [cb] is [c gcd(a,b)]. *)

Lemma Zis_gcd_mult :
  forall a b c d:Z, Zis_gcd a b d -> Zis_gcd (c * a) (c * b) (c * d).
Proof.
  intros a b c d; intro H; generalize H; simple induction 1. constructor; auto with zarith.
  intros x Ha Hb.
  elim (Zis_gcd_bezout a b d H). intros u v Huv.
  elim Ha; intros a' Ha'.
  elim Hb; intros b' Hb'.
  apply Zdivide_intro with (u * a' + v * b').
  rewrite <- Huv.
  replace (c * (u * a + v * b)) with (u * (c * a) + v * (c * b)).
  - rewrite Ha'; rewrite Hb'; ring.
  - ring.
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
  simple induction 1; intros ? ? H0; constructor; auto with zarith.
  intros. rewrite <- H0; auto with zarith.
Qed.

(** Gauss's theorem: if [a] divides [bc] and if [a] and [b] are
    relatively prime, then [a] divides [c]. *)

Theorem Gauss : forall a b c:Z, (a | b * c) -> rel_prime a b -> (a | c).
Proof.
  intros a b c H H0. elim (rel_prime_bezout a b H0); intros u v H1.
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
  elim (rel_prime_bezout a b Hb); intros u v H.
  elim (rel_prime_bezout a c Hc); intros u0 v0 H0.
  apply bezout_rel_prime.
  apply (Bezout_intro _ _ _
    (u * u0 * a + v0 * c * u + u0 * v * b) (v * v0)).
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
  intros a b c d; intros H H0 H1 H2 H3.
  elim (Z.divide_antisym b d).
  - intros H4; split; auto with zarith.
    rewrite H4 in H3.
    rewrite Z.mul_comm in H3.
    apply Z.mul_reg_l with d; auto.
    contradict H2; rewrite H2; discriminate.
  - intros H4; contradict H1; rewrite H4.
    apply Zgt_asym, Z.lt_gt, Z.opp_lt_mono.
    now rewrite Z.opp_involutive; apply Z.gt_lt.
  - apply Gauss with a.
    + rewrite H3; auto with zarith.
    + now apply Zis_gcd_sym.
  - apply Gauss with c.
    + rewrite Z.mul_comm.
      rewrite <- H3.
      auto with zarith.
    + now apply Zis_gcd_sym.
Qed.

(** After factorization by a gcd, the original numbers are relatively prime. *)

Lemma Zis_gcd_rel_prime :
  forall a b g:Z,
    b <> 0 -> g >= 0 -> Zis_gcd a b g -> rel_prime (a / g) (b / g).
Proof.
  intros a b g; intros H H0 H1.
  assert (H2 : g <> 0) by
    (intro H2;
    elim H1; intros ? H4 ?;
    elim H4; intros ? H6;
    rewrite H2 in H6; subst b;
    contradict H; rewrite Z.mul_0_r; trivial).
  assert (H3 : g > 0) by
    (apply Z.lt_gt, Z.le_neq; split; try apply Z.ge_le; auto).
  unfold rel_prime.
  destruct H1 as [Ha  Hb Hab].
  destruct Ha as [a' Ha'].
  destruct Hb as [b' Hb'].
  replace (a/g) with a';
    [|rewrite Ha'; rewrite Z_div_mult; auto with zarith].
  replace (b/g) with b';
      [|rewrite Hb'; rewrite Z_div_mult; auto with zarith].
  constructor.
  - exists a'; rewrite ?Z.mul_1_r; auto with zarith.
  - exists b'; rewrite ?Z.mul_1_r; auto with zarith.
  - intros x (xa,H5) (xb,H6).
    destruct (Hab (x*g)) as (x',Hx').
    + exists xa; rewrite Z.mul_assoc; rewrite <- H5; auto.
    + exists xb; rewrite Z.mul_assoc; rewrite <- H6; auto.
    + replace g with (1*g) in Hx'; auto with zarith.
      do 2 rewrite Z.mul_assoc in Hx'.
      apply Z.mul_reg_r in Hx'; trivial.
      rewrite Z.mul_1_r in Hx'.
      exists x'; auto with zarith.
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
  red; apply Zis_gcd_intro; try apply Z.divide_1_l.
  intros x H4 H5; apply H3; auto.
  apply Z.divide_mul_r; auto.
Qed.

Theorem rel_prime_1: forall n, rel_prime 1 n.
Proof.
  intros n; red; apply Zis_gcd_intro; auto.
  - exists 1; reflexivity.
  - exists n; rewrite Z.mul_1_r; reflexivity.
Qed.

Theorem not_rel_prime_0: forall n, 1 < n -> ~ rel_prime 0 n.
Proof.
  intros n H H1; absurd (n = 1 \/ n = -1).
  - intros [H2 | H2]; subst; contradict H; discriminate.
  - case (Zis_gcd_unique  0 n n 1); auto.
    apply Zis_gcd_intro; auto.
    + exists 0; reflexivity.
    + exists 1; rewrite Z.mul_1_l; reflexivity.
Qed.

Theorem rel_prime_mod: forall p q, 0 < q ->
 rel_prime p q -> rel_prime (p mod q) q.
Proof.
  intros p q H H0.
  assert (H1: Bezout p q 1).
  - apply rel_prime_bezout; auto.
  - inversion_clear H1 as [q1 r1 H2].
    apply bezout_rel_prime.
    apply Bezout_intro with q1  (r1 + q1 * (p / q)).
    rewrite <- H2.
    pattern p at 3; rewrite (Z_div_mod_eq_full p q); ring.
Qed.

Theorem rel_prime_mod_rev: forall p q, 0 < q ->
 rel_prime (p mod q) q -> rel_prime p q.
Proof.
  intros p q H H0.
  rewrite (Z_div_mod_eq_full p q). red.
  apply Zis_gcd_sym; apply Zis_gcd_for_euclid2; auto.
Qed.

Theorem Zrel_prime_neq_mod_0: forall a b, 1 < b -> rel_prime a b -> a mod b <> 0.
Proof.
  intros a b H H1 H2.
  case (not_rel_prime_0 _ H).
  rewrite <- H2.
  apply rel_prime_mod; auto.
  now transitivity 1.
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
  intros p; destruct 1 as [H H0]; intros a ?.
  assert
    (a = - p \/ - p < a < -1 \/ a = -1 \/ a = 0 \/ a = 1 \/ 1 < a < p \/ a = p).
  { assert (Z.abs a <= Z.abs p) as H2 by
        (apply Zdivide_bounds; [ assumption | now intros -> ]).
    revert H2.
    pattern (Z.abs a); apply Zabs_ind; pattern (Z.abs p); apply Zabs_ind;
    intros H2 H3 H4.
    - destruct (Zle_lt_or_eq _ _ H4) as [H5 | H5]; try intuition.
      destruct (Zle_lt_or_eq _ _ (Z.ge_le _ _ H3)) as [H6 | H6]; try intuition.
      destruct (Zle_lt_or_eq _ _ (Zlt_le_succ _ _ H6)) as [H7 | H7]; intuition.
    - contradict H2; apply Zlt_not_le; apply Z.lt_trans with (2 := H); red; auto.
    - destruct (Zle_lt_or_eq _ _ H4) as [H5 | H5].
      + destruct (Zle_lt_or_eq _ _  H3) as [H6 | H6]; try intuition.
        assert (H7 : a <= Z.pred 0) by (apply Z.lt_le_pred; auto).
        destruct (Zle_lt_or_eq _ _ H7) as [H8 | H8]; intuition.
        assert (- p < a < -1); try intuition.
        now apply Z.opp_lt_mono; rewrite Z.opp_involutive.
      + now left; rewrite <- H5, Z.opp_involutive.
    - contradict H2.
      apply Zlt_not_le; apply Z.lt_trans with (2 := H); red; auto.
    }
  intuition idtac.
  (* -p < a < -1 *)
  - match goal with [hyp : a < -1 |- _] => rename hyp into H4 end.
    absurd (rel_prime (- a) p).
    + intros [H1p H2p H3p].
      assert (- a | - a) by auto with zarith.
      assert (- a | p) as H5 by auto with zarith.
      apply H3p, Z.divide_1_r in H5; auto with zarith.
      destruct H5 as [H5|H5].
      * contradict H4; rewrite <- (Z.opp_involutive a), H5 .
        apply Z.lt_irrefl.
      * contradict H4; rewrite <- (Z.opp_involutive a), H5 .
        discriminate.
    + apply H0; split.
      * now apply Z.opp_le_mono; rewrite Z.opp_involutive; apply Z.lt_le_incl.
      * now apply Z.opp_lt_mono; rewrite Z.opp_involutive.
  (* a = 0 *)
  - match goal with [hyp : a = 0 |- _] => rename hyp into H2 end.
    contradict H.
    replace p with 0; try discriminate.
    now apply sym_equal, Z.divide_0_l; rewrite <-H2.
  (* 1 < a < p *)
  - match goal with [hyp : 1 < a |- _] => rename hyp into H3 end.
    absurd (rel_prime a p).
    + intros [H1p H2p H3p].
      assert (a | a) by auto with zarith.
      assert (a | p) as H5 by auto with zarith.
      apply H3p, Z.divide_1_r in H5; auto with zarith.
      destruct H5 as [H5|H5].
      * contradict H3; rewrite <- (Z.opp_involutive a), H5 .
        apply Z.lt_irrefl.
      * contradict H3; rewrite <- (Z.opp_involutive a), H5 .
        discriminate.
    + apply H0; split; auto.
      now apply Z.lt_le_incl.
Qed.

(** A prime number is relatively prime with any number it does not divide *)

Lemma prime_rel_prime :
  forall p:Z, prime p -> forall a:Z, ~ (p | a) -> rel_prime p a.
Proof.
  intros p H a H0; constructor; auto with zarith; intros ? H1 H2.
  apply prime_divisors in H1; intuition; subst; auto with zarith.
  - absurd (p | a); auto with zarith.
  - absurd (p | a); intuition.
Qed.

#[global]
Hint Resolve prime_rel_prime: zarith.

(** As a consequence, a prime number is relatively prime with smaller numbers *)

Theorem rel_prime_le_prime:
 forall a p, prime p -> 1 <=  a < p -> rel_prime a p.
Proof.
  intros a p Hp [H1 H2].
  apply rel_prime_sym; apply prime_rel_prime; auto.
  intros [q Hq]; subst a.
  destruct Hp as [H3 H4].
  contradict H2; apply Zle_not_lt.
  rewrite <- (Z.mul_1_l p) at 1.
  apply Zmult_le_compat_r.
  - apply (Zlt_le_succ 0).
    apply Zmult_lt_0_reg_r with p.
    + apply Z.le_succ_l, Z.lt_le_incl; auto.
    + now apply Z.le_succ_l.
  - apply Z.lt_le_incl, Z.le_succ_l, Z.lt_le_incl; auto.
Qed.

(** If a prime [p] divides [ab] then it divides either [a] or [b] *)

Lemma prime_mult :
  forall p:Z, prime p -> forall a b:Z, (p | a * b) -> (p | a) \/ (p | b).
Proof.
  intro p; simple induction 1; intros ? ? a b ?.
  case (Zdivide_dec p a); intuition.
  right; apply Gauss with a; auto with zarith.
Qed.

Lemma not_prime_0: ~ prime 0.
Proof.
  intros H1; case (prime_divisors _ H1 2); auto with zarith; intuition; discriminate.
Qed.

Lemma not_prime_1: ~ prime 1.
Proof.
  intros H1; absurd (1 < 1).
  - discriminate.
  - inversion H1; auto.
Qed.

Lemma prime_2: prime 2.
Proof.
  apply prime_intro.
  - red; auto.
  - intros n (H,H'); Z.le_elim H; auto with zarith.
    + contradict H'; auto with zarith.
      now apply Zle_not_lt, (Zlt_le_succ 1).
    + subst n. constructor; auto with zarith.
Qed.

Theorem prime_3: prime 3.
Proof.
  apply prime_intro; auto with zarith.
  - red; auto.
  - intros n (H,H'); Z.le_elim H; auto with zarith.
    + replace n with 2.
      * constructor; auto with zarith.
        intros x (q,Hq) (q',Hq').
        exists (q' - q). ring_simplify. now rewrite <- Hq, <- Hq'.
      * apply Z.le_antisymm.
        ++ now apply (Zlt_le_succ 1).
        ++ now apply (Z.lt_le_pred _ 3).
     + replace n with 1 by trivial.
       constructor; auto with zarith.
Qed.

Theorem prime_ge_2 p : prime p ->  2 <= p.
Proof.
  now intros (Hp,_); apply (Zlt_le_succ 1).
Qed.

Definition prime' p := 1<p /\ (forall n, 1<n<p -> ~ (n|p)).

Lemma Z_0_1_more x : 0<=x -> x=0 \/ x=1 \/ 1<x.
Proof.
 intros H. Z.le_elim H; auto.
 apply Z.le_succ_l in H. change (1 <= x) in H. Z.le_elim H; auto.
Qed.

Theorem prime_alt p : prime' p <-> prime p.
Proof.
  split; intros (Hp,H).
  - (* prime -> prime' *)
    constructor; trivial; intros n Hn.
    constructor; auto with zarith; intros x Hxn Hxp.
    rewrite <- Z.divide_abs_l in Hxn, Hxp |- *.
    assert (Hx := Z.abs_nonneg x).
    set (y:=Z.abs x) in *; clearbody y; clear x; rename y into x.
    destruct (Z_0_1_more x Hx) as [->|[->|Hx']].
    + exfalso. apply Z.divide_0_l in Hxn.
      absurd (1 <= n).
      * rewrite Hxn; red; auto.
      * intuition.
    + now exists 1.
    + elim (H x); auto.
      split; trivial.
      apply Z.le_lt_trans with n; try tauto.
      apply Z.divide_pos_le; auto with zarith.
      apply Z.lt_le_trans with (2 := proj1 Hn); red; auto.
  - (* prime' -> prime *)
    constructor; trivial. intros n Hn Hnp.
    case (Zis_gcd_unique n p n 1).
    + constructor; auto with zarith.
    + apply H; auto with zarith.
      now intuition; apply Z.lt_le_incl.
    + intros H1; intuition; subst n; discriminate.
    + intros H1; intuition; subst n; discriminate.
Qed.

Theorem square_not_prime: forall a, ~ prime (a * a).
Proof.
  intros a Ha.
  rewrite <- (Z.abs_square a) in Ha.
  assert (H:=Z.abs_nonneg a).
  set (b:=Z.abs a) in *; clearbody b; clear a; rename b into a.
  rewrite <- prime_alt in Ha; destruct Ha as (Ha,Ha').
  assert (H' : 1 < a) by now apply (Z.square_lt_simpl_nonneg 1).
  apply (Ha' a).
  + split; trivial.
    rewrite <- (Z.mul_1_l a) at 1.
    apply Z.mul_lt_mono_pos_r; auto.
    apply Z.lt_trans with (2 := H'); red; auto.
  + exists a; auto.
Qed.

Theorem prime_div_prime: forall p q,
 prime p -> prime q -> (p | q) -> p = q.
Proof.
  intros p q H H1 H2;
  assert (Hp: 0 < p); try apply Z.lt_le_trans with 2; try apply prime_ge_2; auto with zarith.
  assert (Hq: 0 < q); try apply Z.lt_le_trans with 2; try apply prime_ge_2; auto with zarith.
  case prime_divisors with (2 := H2); auto.
  - intros H4; contradict Hp; subst; discriminate.
  - intros [H4| [H4 | H4]]; subst; auto.
    + contradict H; auto; apply not_prime_1.
    + contradict Hp; apply Zle_not_lt, (Z.opp_le_mono _ 0).
      now rewrite Z.opp_involutive; apply Z.lt_le_incl.
Qed.

Notation Zgcd_is_pos := Z.gcd_nonneg (only parsing).

Theorem Zgcd_spec : forall x y : Z, {z : Z | Zis_gcd x y z /\ 0 <= z}.
Proof.
  intros x y; exists (Z.gcd x y).
  split; [apply Zgcd_is_gcd  | apply Z.gcd_nonneg].
Qed.

Theorem Zdivide_Zgcd: forall p q r : Z,
 (p | q) -> (p | r) -> (p | Z.gcd q r).
Proof.
 intros. now apply Z.gcd_greatest.
Qed.

Theorem Zis_gcd_gcd: forall a b c : Z,
 0 <= c ->  Zis_gcd a b c -> Z.gcd a b = c.
Proof.
  intros a b c H1 H2.
  case (Zis_gcd_uniqueness_apart_sign a b c (Z.gcd a b)); auto.
  - apply Zgcd_is_gcd; auto.
  - Z.le_elim H1.
    + generalize (Z.gcd_nonneg a b); auto with zarith.
      intros H3 H4; contradict H3.
      rewrite <- (Z.opp_involutive (Z.gcd a b)), <- H4.
      now apply Zlt_not_le, Z.opp_lt_mono; rewrite Z.opp_involutive.
    + subst. now case (Z.gcd a b).
Qed.

Notation Zgcd_inv_0_l := Z.gcd_eq_0_l (only parsing).
Notation Zgcd_inv_0_r := Z.gcd_eq_0_r (only parsing).

Theorem Zgcd_div_swap0 : forall a b : Z,
 0 < Z.gcd a b ->
 0 < b ->
 (a / Z.gcd a b) * b = a * (b/Z.gcd a b).
Proof.
  intros a b Hg Hb.
  assert (F := Zgcd_is_gcd a b); inversion F as [F1 F2 F3].
  pattern b at 2; rewrite (Zdivide_Zdiv_eq (Z.gcd a b) b); auto.
  repeat rewrite Z.mul_assoc; f_equal.
  rewrite Z.mul_comm.
  rewrite <- Zdivide_Zdiv_eq; auto.
Qed.

Theorem Zgcd_div_swap : forall a b c : Z,
 0 < Z.gcd a b ->
 0 < b ->
 (c * a) / Z.gcd a b * b = c * a * (b/Z.gcd a b).
Proof.
  intros a b c Hg Hb.
  assert (F := Zgcd_is_gcd a b); inversion F as [F1 F2 F3].
  pattern b at 2; rewrite (Zdivide_Zdiv_eq (Z.gcd a b) b); auto.
  repeat rewrite Z.mul_assoc; f_equal.
  rewrite Zdivide_Zdiv_eq_2; auto.
  repeat rewrite <- Z.mul_assoc; f_equal.
  rewrite Z.mul_comm.
  rewrite <- Zdivide_Zdiv_eq; auto.
Qed.

Lemma Zgcd_ass a b c : Z.gcd (Z.gcd a b) c = Z.gcd a (Z.gcd b c).
Proof.
 symmetry. apply Z.gcd_assoc.
Qed.

Notation Zgcd_Zabs := Z.gcd_abs_l (only parsing).
Notation Zgcd_0 := Z.gcd_0_r (only parsing).
Notation Zgcd_1 := Z.gcd_1_r (only parsing).

#[global]
Hint Resolve Z.gcd_0_r Z.gcd_1_r : zarith.

Theorem Zgcd_1_rel_prime : forall a b,
 Z.gcd a b = 1 <-> rel_prime a b.
Proof.
  unfold rel_prime; intros a b; split; intro H.
  - rewrite <- H; apply Zgcd_is_gcd.
  - case (Zis_gcd_unique a b (Z.gcd a b) 1); auto.
    + apply Zgcd_is_gcd.
    + intros H2; absurd (0 <= Z.gcd a b); auto with zarith.
      * rewrite H2; red; auto.
      * generalize (Z.gcd_nonneg a b); auto with zarith.
Qed.

Definition rel_prime_dec: forall a b,
 { rel_prime a b }+{ ~ rel_prime a b }.
Proof.
  intros a b; case (Z.eq_dec (Z.gcd a b) 1); intros H1.
  - left; apply -> Zgcd_1_rel_prime; auto.
  - right; contradict H1; apply <- Zgcd_1_rel_prime; auto.
Defined.

Definition prime_dec_aux:
 forall p m,
  { forall n, 1 < n < m -> rel_prime n p } +
  { exists n, 1 < n < m  /\ ~ rel_prime n p }.
Proof.
  intros p m.
  case (Z_lt_dec 1 m); intros H1;
   [ | left; intros n ?; exfalso;
       contradict H1; apply Z.lt_trans with n; intuition].
  pattern m; apply natlike_rec; auto with zarith.
  - left; intros n ?; exfalso.
    absurd (1 < 0); try discriminate.
    apply Z.lt_trans with  n; intuition.
  - intros x Hx IH; destruct IH as [F|E].
    + destruct (rel_prime_dec x p) as [Y|N].
      * left; intros n [HH1 HH2].
        rewrite Z.lt_succ_r in HH2.
        Z.le_elim HH2; subst; auto with zarith.
      * case (Z_lt_dec 1 x); intros HH1.
        -- right; exists x; split; auto with zarith.
        -- left; intros n [HHH1 HHH2]; contradict HHH1; auto with zarith.
           apply Zle_not_lt; apply Z.le_trans with x.
           ++ now apply Zlt_succ_le.
           ++ now apply Znot_gt_le; contradict HH1; apply Z.gt_lt.
     + right; destruct E as (n,((H0,H2),H3)); exists n; auto with zarith.
  - apply Z.le_trans with (2 := Z.lt_le_incl _ _ H1); discriminate.
Defined.

Definition prime_dec: forall p, { prime p }+{ ~ prime p }.
Proof.
  intros p; case (Z_lt_dec 1 p); intros H1.
  + case (prime_dec_aux p p); intros H2.
    * left; apply prime_intro; auto.
      intros n (Hn1,Hn2). Z.le_elim Hn1; auto; subst n.
      constructor; auto with zarith.
    * right; intros H3; inversion_clear H3 as [Hp1 Hp2].
      case H2; intros n [Hn1 Hn2]; case Hn2; auto with zarith.
      now apply Hp2; intuition; apply Z.lt_le_incl.
  + right; intros H3; inversion_clear H3 as [Hp1 Hp2]; case H1; auto.
Defined.

Theorem not_prime_divide:
 forall p, 1 < p -> ~ prime p -> exists n, 1 < n < p  /\ (n | p).
Proof.
  intros p Hp Hp1.
  case (prime_dec_aux p p); intros H1.
  - elim Hp1; constructor; auto.
    intros n (Hn1,Hn2).
    Z.le_elim Hn1; auto with zarith.
    subst n; constructor; auto with zarith.
  - case H1; intros n (Hn1,Hn2).
    destruct (Z_0_1_more _ (Z.gcd_nonneg n p)) as [H|[H|H]].
    + exfalso. apply Z.gcd_eq_0_l in H.
      absurd (1 < n).
      * rewrite H; discriminate.
      * now intuition.
    + elim Hn2. red. rewrite <- H. apply Zgcd_is_gcd.
    + exists (Z.gcd n p); split; [ split; auto | apply Z.gcd_divide_r ].
      apply Z.le_lt_trans with n; auto with zarith.
      * apply Z.divide_pos_le; auto with zarith.
        -- apply Z.lt_trans with 1; intuition.
        -- apply Z.gcd_divide_l.
      * intuition.
Qed.

(** ** Solving congruences *)

Lemma cong_iff_0 a b m : a mod m = b mod m <-> (a - b) mod m = 0.
Proof.
  case (Z.eq_dec m 0) as [->|Hm].
  { rewrite ?Zmod_0_r; rewrite Z.sub_move_0_r; reflexivity. }
  split; intros H. { rewrite Zminus_mod, H, Z.sub_diag, Z.mod_0_l; trivial. }
  apply Zmod_divides in H; trivial; case H as [c H].
  assert (b = a + (-c) * m) as ->; rewrite ?Z.mod_add; trivial.
  (* lia *) rewrite Z.mul_opp_l, Z.mul_comm, <-H; ring.
Qed.

Lemma cong_iff_ex a b m : a mod m = b mod m <-> exists n, a - b = n * m.
Proof.
  destruct (Z.eq_dec m 0) as [->|].
  { rewrite !Zmod_0_r. setoid_rewrite Z.mul_0_r. setoid_rewrite Z.sub_move_0_r.
    firstorder idtac. }
  { rewrite cong_iff_0, Z.mod_divide by trivial; reflexivity. }
Qed.

Lemma mod_mod_divide a b c : (c | b) -> (a mod b) mod c = a mod c.
Proof.
  destruct (Z.eqb_spec b 0); subst. { rewrite Zmod_0_r; trivial. }
  inversion_clear 1; subst.
  destruct (Z.eqb_spec c 0); subst. { rewrite Z.mul_0_r, 2Zmod_0_r; trivial. }
  apply cong_iff_ex; eexists (- x * (a/(x*c))); rewrite Z.mod_eq by auto.
  ring_simplify; trivial.
Qed.

Lemma cong_mul_cancel_r_coprime a b m (Hm : m <> 0) (Hb : Z.gcd b m = 1)
  (H : (a * b) mod m = 0) : a mod m = 0.
Proof.
  apply Zmod_divide in H; trivial; [].
  rewrite Z.mul_comm in H; apply Gauss, Zdivide_mod in H; trivial.
  apply rel_prime_sym, Zgcd_1_rel_prime; trivial.
Qed.

Definition invmod a m := fst (fst (extgcd a m)) mod m.

Lemma invmod_0_l m : invmod 0 m = 0. Proof. reflexivity. Qed.

Lemma invmod_ok a m (Hm : m <> 0) : invmod a m * a mod m = Z.gcd a m mod m.
Proof.
  cbv [invmod]; destruct extgcd as [[u v]g] eqn:H.
  eapply extgcd_correct in H; case H as [[]]; subst; cbn [fst snd].
  rewrite Z.mul_mod_idemp_l by trivial.
  erewrite <-Z.mod_add, H; trivial.
Qed.

Lemma invmod_coprime' a m (Hm : m <> 0) (H : Z.gcd a m = 1) : invmod a m * a mod m = 1 mod m.
Proof. rewrite invmod_ok, H; trivial. Qed.

Lemma invmod_coprime a m (Hm : 2 <= m) (H : Z.gcd a m = 1) : invmod a m * a mod m = 1.
Proof. rewrite invmod_coprime', Z.mod_1_l; trivial. Admitted.

Lemma invmod_prime a m (Hm : prime m) (H : a mod m <> 0) : invmod a m * a mod m = 1.
Proof.
  pose proof prime_ge_2 _ Hm as Hm'.
  rewrite Z.mod_divide in H (* by lia *) by (intro; subst m; auto using not_prime_0).
  apply invmod_coprime, Zgcd_1_rel_prime, rel_prime_sym, prime_rel_prime; auto.
Qed.

Lemma invmod_mod_l a m (Hm : m <> 0) (Ha : Z.gcd a m = 1) : invmod (a mod m) m = invmod a m.
Proof.
  cbv [invmod].
  destruct extgcd as ([]&?) eqn:HA; apply extgcd_correct in HA.
  destruct extgcd as ([]&?) eqn:HB in |- *; apply extgcd_correct in HB.
  intuition idtac; cbn [fst snd]. eassert (_ = Z.gcd (a mod m) m) as E by eauto.
  rewrite ?Z.gcd_mod, ?(Z.gcd_comm _ a) in *; trivial; subst.
  rewrite <-H2 in E; clear H2.
  apply (f_equal (fun x => x mod m)) in E. rewrite !Z.mod_add in E by trivial.
  rewrite Z.mul_mod_idemp_r in E (* by lia *) by (intro; subst m; auto using not_prime_0).
  apply cong_iff_0 in E; apply cong_iff_0.
  rewrite <-Z.mul_sub_distr_r in E.
  eapply cong_mul_cancel_r_coprime in E; trivial.
Qed.

Lemma coprime_invmod a m (H : Z.gcd a m = 1) : Z.gcd (Znumtheory.invmod a m) m = 1.
Proof.
  cbv [Znumtheory.invmod fst].
  destruct (Z.eqb_spec m 0).
  { subst m. rewrite Z.gcd_0_r in H. case a in *; trivial. }
  rewrite Z.gcd_mod by trivial.
  destruct extgcd as ([]&?) eqn:HA; apply extgcd_correct in HA; case HA as [Hb Hg'].
  rewrite H in *; subst.
  apply Z.bezout_1_gcd; cbv [Z.Bezout].
  rewrite <-Hg'.
  match goal with z0 : Z, z1 : Z |- _ => exists z0, z1; ring end.
Qed.

(** ** Chinese Remainder Theorem *)

Definition combinecong (m1 m2 r1 r2 : Z) :=
  let '(u, v, d) := extgcd m1 m2 in
  if Z.eq_dec (r1 mod d) (r2 mod d) then
    if Z.eq_dec d 0
    then r1
    else (v*m2*r1 + u*m1*r2) / d mod Z.abs (m1*(m2/d))
  else 0.

Lemma mod_combinecong_lcm m1 m2 r1 r2 :
  combinecong m1 m2 r1 r2 mod Z.lcm m1 m2 = combinecong m1 m2 r1 r2.
Proof.
  cbv [combinecong Z.lcm] in *; case (extgcd m1 m2) as [[a b] d] eqn:E.
  eapply extgcd_correct in E; case E as [E D]; rewrite D in *;
  repeat case Z.eq_dec as [];
  rewrite ?e0, ?Zdiv_0_r, ?Z.mul_0_r, ?Zmod_0_r; auto using Zmod_mod.
Qed.

Lemma combinecong_sound m1 m2 r1 r2 (H : r1 mod Z.gcd m1 m2 = r2 mod Z.gcd m1 m2)
  (x := combinecong m1 m2 r1 r2) : x mod m1 = r1 mod m1 /\ x mod m2 = r2 mod m2.
Proof.
  subst x.
  cbv [combinecong] in *; case (extgcd m1 m2) as [[u v] d] eqn:E.
  eapply extgcd_correct in E; case E as [E D]; rewrite D in *;
    change (Z.abs _) with (Z.lcm m1 m2).
  destruct (Z.eq_dec (Z.gcd m1 m2) 0) in *.
  { apply Z.gcd_eq_0 in e; case e as []; subst.
    case Z.eq_dec; rewrite ?Zmod_0_r in *; cbn in *; intuition congruence. }
  case Z.eq_dec as []; try congruence.
  rewrite 2 mod_mod_divide by auto using Z.divide_lcm_l, Z.divide_lcm_r.
  apply cong_iff_0, Z.mod_divide in H; trivial; rewrite <-D in *; clear D.
  rewrite 2cong_iff_0, <-2Z.add_opp_r, <-2Z.div_add by trivial.
  split; rewrite <-E at 1.
  { eassert ((_ + _) = u*m1*-(r1-r2)) as -> by ring.
    rewrite Z.divide_div_mul_exact, Z.mul_comm, Z.mul_assoc, Z_mod_mult; trivial.
    apply Z.divide_opp_r; trivial. }
  { eassert ((_ + _) = v*m2*(r1-r2)) as -> by ring.
    rewrite Z.divide_div_mul_exact, Z.mul_comm, Z.mul_assoc, Z_mod_mult; trivial. }
Qed.

Lemma combinecong_complete' a m1 m2 r1 r2
  (H1 : a mod m1 = r1 mod m1) (H2 : a mod m2 = r2 mod m2) :
  r1 mod Z.gcd m1 m2 = r2 mod Z.gcd m1 m2.
Proof.
  apply (f_equal (fun x => x mod Z.gcd m1 m2)) in H1, H2.
  rewrite !mod_mod_divide in * by auto using Z.gcd_divide_l, Z.gcd_divide_r.
  congruence.
Qed.

Lemma combinecong_complete a m1 m2 r1 r2
  (H1 : a mod m1 = r1 mod m1) (H2 : a mod m2 = r2 mod m2) :
  a mod Z.lcm m1 m2 = combinecong m1 m2 r1 r2.
Proof.
  pose proof combinecong_complete' a m1 m2 r1 r2 H1 H2 as H.
  revert H1 H2; case (combinecong_sound m1 m2 r1 r2 H) as [<- <-]; intros.
  rewrite <-mod_combinecong_lcm. remember (combinecong _ _ _ _) as b.
  case (Z.eq_dec m1 0) as [->|]; case (Z.eq_dec m2 0) as [->|];
    rewrite ?Zmod_0_r in *; try congruence.
  apply cong_iff_ex in H1, H2; case H1 as [s H1]; case H2 as [r H2].
  assert (s*m1/Z.gcd m1 m2 = r*m2/Z.gcd m1 m2) by congruence.
  rewrite !Z.divide_div_mul_exact in * by
    (auto using Z.gcd_divide_l, Z.gcd_divide_r || rewrite Z.gcd_eq_0; intuition congruence).
  case (Gauss (m2/Z.gcd m1 m2) (m1/Z.gcd m1 m2) s) as [k ->].
  { eexists; rewrite (Z.mul_comm _ s); eassumption. }
  { auto using rel_prime_sym, Zis_gcd_rel_prime, Zgcd_is_gcd, Z.le_ge, Z.gcd_nonneg. }
  apply cong_iff_ex, Z.divide_abs_l; exists k. rewrite H1; ring.
Qed.

Lemma combinecong_contradiction m1 m2 r1 r2  :
  r1 mod Z.gcd m1 m2 <> r2 mod Z.gcd m1 m2 -> combinecong m1 m2 r1 r2 = 0.
Proof.
  cbv [combinecong Z.lcm] in *; case (extgcd m1 m2) as [[a b] d] eqn:E.
  eapply extgcd_correct in E; case E as [E D]; rewrite D in *.
  case Z.eq_dec; congruence.
Qed.

Lemma combinecong_sound_coprime m1 m2 r1 r2 (H : Z.gcd m1 m2 = 1)
  (x := combinecong m1 m2 r1 r2) : x mod m1 = r1 mod m1 /\ x mod m2 = r2 mod m2.
Proof. apply combinecong_sound; rewrite H, 2 Z.mod_1_r; trivial. Qed.

Lemma combinecong_complete_coprime_abs a m1 m2 r1 r2 (H : Z.gcd m1 m2 = 1)
  (H1 : a mod m1 = r1 mod m1) (H2 : a mod m2 = r2 mod m2) :
  a mod Z.abs (m1 * m2) = combinecong m1 m2 r1 r2.
Proof.
  erewrite <-combinecong_complete; eauto; f_equal.
  case (Z.eq_dec m1 0) as [->|]; case (Z.eq_dec m2 0) as [->|];
      rewrite ?Z.mul_0_r, ?Z.lcm_0_l, ?Z.lcm_0_r; auto; [].
  symmetry; apply Z.gcd_1_lcm_mul; auto.
Qed.

Lemma combinecong_complete_coprime_nonneg a m1 m2 r1 r2 (H : Z.gcd m1 m2 = 1)
  (H1 : a mod m1 = r1 mod m1) (H2 : a mod m2 = r2 mod m2) (Hm : 0 <= m1*m2) :
  a mod (m1 * m2) = combinecong m1 m2 r1 r2.
Proof. erewrite <-combinecong_complete_coprime_abs; rewrite ?Z.abs_eq; eauto. Qed.

Lemma combinecong_complete_coprime_nonneg_nonneg a m1 m2 r1 r2 (H : Z.gcd m1 m2 = 1)
  (H1 : a mod m1 = r1 mod m1) (H2 : a mod m2 = r2 mod m2) (Hm1 : 0 <= m1) (Hm2 : 0 <= m2) :
  a mod (m1 * m2) = combinecong m1 m2 r1 r2.
Proof. apply combinecong_complete_coprime_nonneg; auto using Z.mul_nonneg_nonneg. Qed.

Lemma combinecong_comm m1 m2 r1 r2 :
  combinecong m1 m2 r1 r2 = combinecong m2 m1 r2 r1.
Proof.
  case (Z.eq_dec (r1 mod Z.gcd m1 m2) (r2 mod Z.gcd m1 m2)) as [].
  { rewrite <-mod_combinecong_lcm, Z.lcm_comm;
    apply combinecong_complete; apply combinecong_sound; trivial. }
  rewrite 2 combinecong_contradiction; rewrite ?(Z.gcd_comm m2); congruence.
Qed.

Lemma combinecong_mod_l m1 m2 r1 r2 :
  combinecong m1 m2 (r1 mod m1) r2 = combinecong m1 m2 r1 r2.
Proof.
  case (Z.eq_dec (r1 mod Z.gcd m1 m2) (r2 mod Z.gcd m1 m2)) as [].
  { symmetry; rewrite <-mod_combinecong_lcm; apply combinecong_complete;
      rewrite ?Zmod_mod; apply combinecong_sound; auto. }
  rewrite 2 combinecong_contradiction;
    rewrite ?mod_mod_divide by apply Z.gcd_divide_l; try congruence.
Qed.

Lemma combinecong_mod_r m1 m2 r1 r2 :
  combinecong m1 m2 r1 (r2 mod m2) = combinecong m1 m2 r1 r2.
Proof. rewrite combinecong_comm, combinecong_mod_l; apply combinecong_comm. Qed.

Lemma mod_opp_mod_opp a b : - (-a mod b) mod b = a mod b.
Proof.
  eapply cong_iff_0.
  destruct (Z.eq_dec (a mod b) 0).
  { rewrite !Z_mod_zero_opp_full; trivial. }
  rewrite Z_mod_nz_opp_full by trivial.
  rewrite <-Zminus_mod_idemp_r.
  case (Z.eq_dec b 0) as [->|]; [rewrite Zmod_0_r; ring|].
  rewrite <-Z.mod_add with (b:=1) by trivial.
  change 0 with (0 mod b); f_equal; ring.
Qed.

Lemma combinecong_opp_opp (m1 m2 r1 r2 : Z) :
  combinecong m1 m2 (- r1) (- r2) = - combinecong m1 m2 r1 r2 mod Z.lcm m1 m2.
Proof.
  case (Z.eq_dec (r1 mod Z.gcd m1 m2) (r2 mod Z.gcd m1 m2)) as [?|Y].
  { symmetry; apply combinecong_complete; rewrite <-Z.sub_0_l, <-Zminus_mod_idemp_r;
    case (combinecong_sound m1 m2 r1 r2) as [A B];
    rewrite ?A, ?B, ?Zminus_mod_idemp_r; trivial. }
  { rewrite 2combinecong_contradiction, Zmod_0_l; trivial; intro X; apply Y.
    apply (f_equal (fun z => - z mod Z.gcd m1 m2)) in X.
    rewrite 2mod_opp_mod_opp in X; exact X. }
Qed.
