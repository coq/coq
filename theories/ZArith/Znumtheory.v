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
Require Import Zdiv.
Open Local Scope Z_scope.

(** This file contains some notions of number theory upon Z numbers: 
     - a divisibility predicate [Zdivide]
     - a gcd predicate [gcd]
     - Euclid algorithm [euclid]
     - an efficient [Zgcd] function 
     - a relatively prime predicate [rel_prime]
     - a prime predicate [prime]
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
ring.
pattern a at 2 in |- *; rewrite H2; ring.
assert (q | 1).
rewrite <- Hqq0; auto with zarith.
elim (Zdivide_1 q H); intros.
rewrite H1 in H0; left; omega.
rewrite H1 in H0; right; omega.
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

Lemma Zis_gcd_minus : forall a b d:Z, Zis_gcd a (- b) d -> Zis_gcd b a d.
Proof.
simple induction 1; constructor; intuition.
Qed.

Lemma Zis_gcd_opp : forall a b d:Z, Zis_gcd a b d -> Zis_gcd b a (- d).
Proof.
simple induction 1; constructor; intuition.
Qed.

Hint Resolve Zis_gcd_sym Zis_gcd_0 Zis_gcd_minus Zis_gcd_opp: zarith.

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
apply Z_lt_rec.
clear v3 Hv3; intros.
elim (Z_zerop x); intro.
apply Euclid_intro with (u := u1) (v := u2) (d := u3).
assumption.
apply H2.
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
rewrite H0; rewrite H1; trivial.
ring.
intros; apply H2.
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
elim (Zis_gcd_bezout a b d H); intros.
elim H3; intros.
elim H4; intros.
apply Zdivide_intro with (u * q + v * q0).
rewrite <- H5.
replace (c * (u * a + v * b)) with (u * (c * a) + v * (c * b)).
rewrite H6; rewrite H7; ring.
ring.
Qed.

(** We could obtain a [Zgcd] function via [euclid]. But we propose 
  here a more direct version of a [Zgcd], with better extraction 
  (no bezout coeffs). *)

Definition Zgcd_pos :
  forall a:Z,
    0 <= a -> forall b:Z, {g : Z | 0 <= a -> Zis_gcd a b g /\ g >= 0}.
Proof.
intros a Ha.
apply
 (Z_lt_rec
    (fun a:Z => forall b:Z, {g : Z | 0 <= a -> Zis_gcd a b g /\ g >= 0}));
 try assumption.
intro x; case x.
intros _ b; exists (Zabs b).
  elim (Z_le_lt_eq_dec _ _ (Zabs_pos b)).
    intros H0; split.
    apply Zabs_ind.
    intros; apply Zis_gcd_sym; apply Zis_gcd_0; auto.
    intros; apply Zis_gcd_opp; apply Zis_gcd_0; auto.
    auto with zarith.
    
    intros H0; rewrite <- H0.
    rewrite <- (Zabs_Zsgn b); rewrite <- H0; simpl in |- *.
    split; [ apply Zis_gcd_0 | idtac ]; auto with zarith.
  
intros p Hrec b.
generalize (Z_div_mod b (Zpos p)).
case (Zdiv_eucl b (Zpos p)); intros q r Hqr.
elim Hqr; clear Hqr; intros; auto with zarith.
elim (Hrec r H0 (Zpos p)); intros g Hgkl.
inversion_clear H0.
elim (Hgkl H1); clear Hgkl; intros H3 H4.
exists g; intros.
split; auto.
rewrite H.
apply Zis_gcd_for_euclid2; auto.

intros p Hrec b.
exists 0; intros.
elim H; auto.
Defined.

Definition Zgcd_spec : forall a b:Z, {g : Z | Zis_gcd a b g /\ g >= 0}.
Proof.
intros a; case (Z_gt_le_dec 0 a).
intros; assert (0 <= - a).
omega.
elim (Zgcd_pos (- a) H b); intros g Hgkl.
exists g.
intuition.
intros Ha b; elim (Zgcd_pos a Ha b); intros g; exists g; intuition.
Defined.

Definition Zgcd (a b:Z) := let (g, _) := Zgcd_spec a b in g.

Lemma Zgcd_is_pos : forall a b:Z, Zgcd a b >= 0.
intros a b; unfold Zgcd in |- *; case (Zgcd_spec a b); tauto.
Qed.

Lemma Zgcd_is_gcd : forall a b:Z, Zis_gcd a b (Zgcd a b).
intros a b; unfold Zgcd in |- *; case (Zgcd_spec a b); tauto.
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
intros a b g; intros.
assert (g <> 0).
 intro.
 elim H1; intros. 
 elim H4; intros.
 rewrite H2 in H6; subst b; omega.
unfold rel_prime in |- *.
elim (Zgcd_spec (a / g) (b / g)); intros g' [H3 H4].
assert (H5 := Zis_gcd_mult _ _ g _ H3).
rewrite <- Z_div_exact_2 in H5; auto with zarith.
rewrite <- Z_div_exact_2 in H5; auto with zarith.
elim (Zis_gcd_uniqueness_apart_sign _ _ _ _ H1 H5).
intros; rewrite (Zmult_reg_l 1 g' g); auto with zarith.
intros; rewrite (Zmult_reg_l 1 (- g') g); auto with zarith.
pattern g at 1 in |- *; rewrite H6; ring.

elim H1; intros.
elim H7; intros.
rewrite H9.
replace (q * g) with (0 + q * g).
rewrite Z_mod_plus.
compute in |- *; auto.
omega.
ring.

elim H1; intros.
elim H6; intros.
rewrite H9.
replace (q * g) with (0 + q * g).
rewrite Z_mod_plus.
compute in |- *; auto.
omega.
ring.
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

(** [Zdivide] can be expressed using [Zmod]. *)

Lemma Zmod_divide : forall a b:Z, b > 0 -> a mod b = 0 -> (b | a).
intros a b H H0.
apply Zdivide_intro with (a / b).
pattern a at 1 in |- *; rewrite (Z_div_mod_eq a b H).
rewrite H0; ring.
Qed.

Lemma Zdivide_mod : forall a b:Z, b > 0 -> (b | a) -> a mod b = 0.
intros a b; simple destruct 2; intros; subst.
change (q * b) with (0 + q * b) in |- *.
rewrite Z_mod_plus; auto.
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

(** If a prime [p] divides [ab] then it divides either [a] or [b] *)

Lemma prime_mult :
 forall p:Z, prime p -> forall a b:Z, (p | a * b) -> (p | a) \/ (p | b).
Proof.
intro p; simple induction 1; intros.
case (Zdivide_dec p a); intuition.
right; apply Gauss with a; auto with zarith.
Qed.

