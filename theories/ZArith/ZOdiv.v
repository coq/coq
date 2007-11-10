(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


Require Import BinPos BinNat Nnat ZArith_base ROmega ZArithRing.
Require Export ZOdiv_def.
Require Zdiv.

Open Scope Z_scope.

(** This file provides results about the Round-Toward-Zero Euclidean 
  division [ZOdiv_eucl], whose projections are [ZOdiv] and [ZOmod].
  Definition of this division can be found in file [ZOdiv_def]. 

  This division and the one defined in Zdiv agree only on positive 
  numbers. Otherwise, Zdiv performs Round-Toward-Bottom. 

  The current approach is compatible with the division of usual 
  programming languages such as Ocaml. In addition, it has nicer 
  properties with respect to opposite and other usual operations.
*)

(** Since ZOdiv and Zdiv are not meant to be used concurrently, 
   we reuse the same notation. *)

Infix "/" := ZOdiv : Z_scope.
Infix "mod" := ZOmod (at level 40, no associativity) : Z_scope.

Infix "/" := Ndiv : N_scope.
Infix "mod" := Nmod (at level 40, no associativity) : N_scope.

(** Auxiliary results on the ad-hoc comparison [NPgeb]. *)

Lemma NPgeb_Zge : forall (n:N)(p:positive), 
  NPgeb n p = true -> Z_of_N n >= Zpos p.
Proof.
 destruct n as [|n]; simpl; intros.
 discriminate.
 red; simpl; destruct Pcompare; now auto.
Qed.

Lemma NPgeb_Zlt : forall (n:N)(p:positive), 
  NPgeb n p = false -> Z_of_N n < Zpos p.
Proof.
 destruct n as [|n]; simpl; intros.
 red; auto.
 red; simpl; destruct Pcompare; now auto.
Qed.

(** * Relation between division on N and on Z. *)

Lemma Ndiv_Z0div : forall a b:N, 
  Z_of_N (a/b) = (Z_of_N a / Z_of_N b).
Proof.
  intros.
  destruct a; destruct b; simpl; auto.
  unfold Ndiv, ZOdiv; simpl; destruct Pdiv_eucl; auto.
Qed.

Lemma Nmod_Z0mod : forall a b:N, 
  Z_of_N (a mod b) = (Z_of_N a) mod (Z_of_N b).
Proof.
  intros.
  destruct a; destruct b; simpl; auto.
  unfold Nmod, ZOmod; simpl; destruct Pdiv_eucl; auto.
Qed.

(** * Characterization of this euclidean division. *)

(** First, the usual equation [a=q*b+r]. Notice that [a mod 0] 
   has been chosen to be [a], so this equation holds even for [b=0].
*)

Theorem N_div_mod_eq : forall a b, 
  a = (b * (Ndiv a b) + (Nmod a b))%N.
Proof.
  intros; generalize (Ndiv_eucl_correct a b).
  unfold Ndiv, Nmod; destruct Ndiv_eucl; simpl.
  intro H; rewrite H; rewrite Nmult_comm; auto.
Qed.

Theorem ZO_div_mod_eq : forall a b, 
  a = b * (ZOdiv a b) + (ZOmod a b).
Proof.
  intros; generalize (ZOdiv_eucl_correct a b).
  unfold ZOdiv, ZOmod; destruct ZOdiv_eucl; simpl.
  intro H; rewrite H; rewrite Zmult_comm; auto.
Qed.

(** Then, the inequalities constraining the remainder. *)

Theorem Pdiv_eucl_remainder : forall a b:positive, 
  Z_of_N (snd (Pdiv_eucl a b)) < Zpos b. 
Proof.
  induction a; cbv beta iota delta [Pdiv_eucl]; fold Pdiv_eucl; cbv zeta.
  intros b; generalize (IHa b); case Pdiv_eucl.
    intros q1 r1 Hr1; simpl in Hr1.
    case_eq (NPgeb (2*r1+1) b); intros; unfold snd.
    romega with *.
    apply NPgeb_Zlt; auto.
  intros b; generalize (IHa b); case Pdiv_eucl.
    intros q1 r1 Hr1; simpl in Hr1.
    case_eq (NPgeb (2*r1) b); intros; unfold snd.
    romega with *.
    apply NPgeb_Zlt; auto.
  destruct b; simpl; romega with *.
Qed.

Theorem Nmod_lt : forall (a b:N), b<>0%N -> 
  (a mod b < b)%N.
Proof.
  destruct b as [ |b]; intro H; try solve [elim H;auto].
  destruct a as [ |a]; try solve [compute;auto]; unfold Nmod, Ndiv_eucl.
  generalize (Pdiv_eucl_remainder a b); destruct Pdiv_eucl; simpl.
  romega with *.
Qed.

(** The remainder is bounded by the divisor, in term of absolute values *)

Theorem ZOmod_lt : forall a b:Z, b<>0 -> 
  Zabs (a mod b) < Zabs b.
Proof.
  destruct b as [ |b|b]; intro H; try solve [elim H;auto]; 
  destruct a as [ |a|a]; try solve [compute;auto]; unfold ZOmod, ZOdiv_eucl; 
  generalize (Pdiv_eucl_remainder a b); destruct Pdiv_eucl; simpl; 
  try rewrite Zabs_Zopp; rewrite Zabs_eq; auto; apply Z_of_N_le_0.
Qed.

(** The sign of the remainder is the one of [a]. Due to the possible 
   nullity of [a], a general result is to be stated in the following form:
*)   

Theorem ZOmod_sgn : forall a b:Z, 
  0 <= Zsgn (a mod b) * Zsgn a.
Proof.
  destruct b as [ |b|b]; destruct a as [ |a|a]; simpl; auto with zarith;
  unfold ZOmod, ZOdiv_eucl; destruct Pdiv_eucl;
  simpl; destruct n0; simpl; auto with zarith.
Qed.

(** This can also be said in a simplier way: *)

Theorem Zsgn_pos_iff : forall z, 0 <= Zsgn z <-> 0 <= z.
Proof.
 destruct z; simpl; intuition auto with zarith.
Qed.

Theorem ZOmod_sgn2 : forall a b:Z, 
  0 <= (a mod b) * a.
Proof.
  intros; rewrite <-Zsgn_pos_iff, Zsgn_Zmult; apply ZOmod_sgn.
Qed.  

(** Reformulation of [ZOdiv_lt] and [ZOmod_sgn] in 2 
  then 4 particular cases. *)

Theorem ZOmod_lt_pos : forall a b:Z, 0<=a -> b<>0 ->   
  0 <= a mod b < Zabs b.
Proof.
  intros.
  assert (0 <= a mod b).
   generalize (ZOmod_sgn a b).
   destruct (Zle_lt_or_eq 0 a H).
   rewrite <- Zsgn_pos in H1; rewrite H1; romega with *.
   subst a; simpl; auto.
  generalize (ZOmod_lt a b H0); romega with *.
Qed.

Theorem ZOmod_lt_neg : forall a b:Z, a<=0 -> b<>0 ->   
  -Zabs b < a mod b <= 0.
Proof.
  intros.
  assert (a mod b <= 0).
   generalize (ZOmod_sgn a b).
   destruct (Zle_lt_or_eq a 0 H).
   rewrite <- Zsgn_neg in H1; rewrite H1; romega with *.
   subst a; simpl; auto.
  generalize (ZOmod_lt a b H0); romega with *.
Qed.

Theorem ZOmod_lt_pos_pos : forall a b:Z, 0<=a -> 0<b -> 0 <= a mod b < b.
Proof.
  intros; generalize (ZOmod_lt_pos a b); romega with *.
Qed.

Theorem ZOmod_lt_pos_neg : forall a b:Z, 0<=a -> b<0 -> 0 <= a mod b < -b.
Proof.
  intros; generalize (ZOmod_lt_pos a b); romega with *.
Qed.

Theorem ZOmod_lt_neg_pos : forall a b:Z, a<=0 -> 0<b -> -b < a mod b <= 0.
Proof.
  intros; generalize (ZOmod_lt_neg a b); romega with *.
Qed.

Theorem ZOmod_lt_neg_neg : forall a b:Z, a<=0 -> b<0 -> b < a mod b <= 0.
Proof.
  intros; generalize (ZOmod_lt_neg a b); romega with *.
Qed.

(** * Division and Opposite *)

(* The precise equalities that are invalid with "historic" Zdiv. *)

Theorem ZOdiv_opp_l : forall a b:Z, (-a)/b = -(a/b).
Proof.
 destruct a; destruct b; simpl; auto; 
  unfold ZOdiv, ZOdiv_eucl; destruct Pdiv_eucl; simpl; auto with zarith.
Qed.

Theorem ZOdiv_opp_r : forall a b:Z, a/(-b) = -(a/b).
Proof.
 destruct a; destruct b; simpl; auto; 
  unfold ZOdiv, ZOdiv_eucl; destruct Pdiv_eucl; simpl; auto with zarith.
Qed.

Theorem ZOmod_opp_l : forall a b:Z, (-a) mod b = -(a mod b).
Proof.
 destruct a; destruct b; simpl; auto; 
  unfold ZOmod, ZOdiv_eucl; destruct Pdiv_eucl; simpl; auto with zarith.
Qed.

Theorem ZOmod_opp_r : forall a b:Z, a mod (-b) = a mod b.
Proof.
 destruct a; destruct b; simpl; auto; 
  unfold ZOmod, ZOdiv_eucl; destruct Pdiv_eucl; simpl; auto with zarith.
Qed.

Theorem ZOdiv_opp_opp : forall a b:Z, (-a)/(-b) = a/b.
Proof.
 destruct a; destruct b; simpl; auto; 
  unfold ZOdiv, ZOdiv_eucl; destruct Pdiv_eucl; simpl; auto with zarith.
Qed.

Theorem ZOmod_opp_opp : forall a b:Z, (-a) mod (-b) = -(a mod b).
Proof.
 destruct a; destruct b; simpl; auto; 
  unfold ZOmod, ZOdiv_eucl; destruct Pdiv_eucl; simpl; auto with zarith.
Qed.

(** * Unicity results *)

Definition Remainder a b r := 
  (0 <= a /\ 0 <= r < Zabs b) \/ (a <= 0 /\ -Zabs b < r <= 0).

Definition Remainder_alt a b r := 
  Zabs r < Zabs b /\ 0 <= r * a.

Lemma Remainder_equiv : forall a b r, 
 Remainder a b r <-> Remainder_alt a b r.
Proof.
  unfold Remainder, Remainder_alt; intuition.
  romega with *.
  romega with *.
  rewrite <-(Zmult_opp_opp).
  apply Zmult_le_0_compat; romega.
  assert (0 <= Zsgn r * Zsgn a) by (rewrite <-Zsgn_Zmult, Zsgn_pos_iff; auto). 
  destruct r; simpl Zsgn in *; romega with *.
Qed.

Theorem ZOdiv_mod_unique_full:
 forall a b q r, Remainder a b r -> 
   a = b*q + r -> q = a/b /\ r = a mod b.
Proof.
  destruct 1 as [(H,H0)|(H,H0)]; intros.
  apply Zdiv.Zdiv_mod_unique with b; auto.
  apply ZOmod_lt_pos; auto.
  romega with *.
  rewrite <- H1; apply ZO_div_mod_eq.

  rewrite <- (Zopp_involutive a).
  rewrite ZOdiv_opp_l, ZOmod_opp_l.
  generalize (Zdiv.Zdiv_mod_unique b (-q) (-a/b) (-r) (-a mod b)).
  generalize (ZOmod_lt_pos (-a) b).
  rewrite <-ZO_div_mod_eq, <-Zopp_mult_distr_r, <-Zopp_plus_distr, <-H1.
  romega with *.
Qed.

Theorem ZOdiv_unique_full: 
 forall a b q r, Remainder a b r -> 
  a = b*q + r -> q = a/b.
Proof.
 intros; destruct (ZOdiv_mod_unique_full a b q r); auto.
Qed.

Theorem ZOdiv_unique:
 forall a b q r, 0 <= a -> 0 <= r < b -> 
   a = b*q + r -> q = a/b.
Proof.
  intros; eapply ZOdiv_unique_full; eauto.
  red; romega with *.
Qed.

Theorem ZOmod_unique_full: 
 forall a b q r, Remainder a b r -> 
  a = b*q + r -> r = a mod b.
Proof.
 intros; destruct (ZOdiv_mod_unique_full a b q r); auto.
Qed.

Theorem ZOmod_unique:
 forall a b q r, 0 <= a -> 0 <= r < b -> 
   a = b*q + r -> r = a mod b.
Proof.
  intros; eapply ZOmod_unique_full; eauto.
  red; romega with *.
Qed.

(** * Basic values of divisions and modulo. *)

Lemma ZOmod_0_l: forall a, 0 mod a = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma ZOmod_0_r: forall a, a mod 0 = a.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma ZOdiv_0_l: forall a, 0/a = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma ZOdiv_0_r: forall a, a/0 = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma ZOmod_1_r: forall a, a mod 1 = 0.
Proof.
  intros; symmetry; apply ZOmod_unique_full with a; auto with zarith.
  rewrite Remainder_equiv; red; simpl; auto with zarith.
Qed.

Lemma ZOdiv_1_r: forall a, a/1 = a.
Proof.
  intros; symmetry; apply ZOdiv_unique_full with 0; auto with zarith.
  rewrite Remainder_equiv; red; simpl; auto with zarith.
Qed.

Hint Resolve ZOmod_0_l ZOmod_0_r ZOdiv_0_l ZOdiv_0_r ZOdiv_1_r ZOmod_1_r 
 : zarith.

Lemma ZOdiv_1_l: forall a, 1 < a -> 1/a = 0.
Proof.
  intros; symmetry; apply ZOdiv_unique with 1; auto with zarith.
Qed.

Lemma ZOmod_1_l: forall a, 1 < a ->  1 mod a = 1.
Proof.
  intros; symmetry; apply ZOmod_unique with 0; auto with zarith.
Qed.

Lemma ZO_div_same : forall a:Z, a<>0 -> a/a = 1.
Proof.
  intros; symmetry; apply ZOdiv_unique_full with 0; auto with *.
  rewrite Remainder_equiv; red; simpl; romega with *.
Qed.

Lemma ZO_mod_same : forall a, a mod a = 0.
Proof.
  destruct a; intros; symmetry.
  compute; auto.
  apply ZOmod_unique with 1; auto with *; romega with *.
  apply ZOmod_unique_full with 1; auto with *; red; romega with *.
Qed.

Lemma ZO_mod_mult : forall a b, (a*b) mod b = 0.
Proof.
  intros a b; destruct (Z_eq_dec b 0) as [Hb|Hb].
  subst; simpl; rewrite ZOmod_0_r; auto with zarith.
  symmetry; apply ZOmod_unique_full with a; [ red; romega with * | ring ].
Qed.

Lemma ZO_div_mult : forall a b:Z, b <> 0 -> (a*b)/b = a.
Proof.
  intros; symmetry; apply ZOdiv_unique_full with 0; auto with zarith; 
   [ red; romega with * | ring].
Qed.

(** * Order results about ZOmod and ZOdiv *)

(* Division of positive numbers is positive. *)

Lemma ZO_div_pos: forall a b, 0 <= a -> 0 <= b -> 0 <= a/b.
Proof.
  intros.
  destruct (Zle_lt_or_eq 0 b H0).
  assert (H2:=ZOmod_lt_pos_pos a b H H1).
  rewrite (ZO_div_mod_eq a b) in H.
  destruct (Z_lt_le_dec (a/b) 0); auto.
  assert (b*(a/b) <= -b).
   replace (-b) with (b*-1); [ | ring].
   apply Zmult_le_compat_l; auto with zarith.
  romega.
  subst b; rewrite ZOdiv_0_r; auto.
Qed.

(** As soon as the divisor is greater or equal than 2, 
    the division is strictly decreasing. *)

Lemma ZO_div_lt : forall a b:Z, 0 < a -> 2 <= b -> a/b < a.
Proof.
  intros. 
  assert (Hb : 0 < b) by romega.
  assert (H1 : 0 <= a/b) by (apply ZO_div_pos; auto with zarith).
  assert (H2 : 0 <= a mod b < b) by (apply ZOmod_lt_pos_pos; auto with zarith).
  destruct (Zle_lt_or_eq 0 (a/b) H1) as [H3|H3]; [ | rewrite <- H3; auto].
  pattern a at 2; rewrite (ZO_div_mod_eq a b).
  apply Zlt_le_trans with (2*(a/b)).
  romega.
  apply Zle_trans with (b*(a/b)).
  apply Zmult_le_compat_r; auto.
  romega.
Qed.

(** A division of a small number by a bigger one yields zero. *)

Theorem ZOdiv_small: forall a b, 0 <= a < b -> a/b = 0.
Proof.
  intros a b H; apply sym_equal; apply ZOdiv_unique with a; auto with zarith.
Qed.

(** Same situation, in term of modulo: *)

Theorem ZOmod_small: forall a n, 0 <= a < n -> a mod n = a.
Proof.
  intros a b H; apply sym_equal; apply ZOmod_unique with 0; auto with zarith.
Qed.

(** [Zge] is compatible with a positive division. *)

Lemma ZO_div_monotone_pos : forall a b c:Z, 0<=c -> 0<=a<=b -> a/c <= b/c.
Proof.
  intros.
  destruct H0.
  destruct (Zle_lt_or_eq 0 c H); 
   [ clear H | subst c; do 2 rewrite ZOdiv_0_r; auto].
  generalize (ZO_div_mod_eq a c).
  generalize (ZOmod_lt_pos_pos a c H0 H2).
  generalize (ZO_div_mod_eq b c).
  generalize (ZOmod_lt_pos_pos b c (Zle_trans _ _ _ H0 H1) H2).
  intros.
  elim (Z_le_gt_dec (a / c) (b / c)); auto with zarith.
  intro.
  absurd (a - b >= 1).
  omega.
  replace (a-b) with (c * (a/c-b/c) + a mod c - b mod c) by 
    (symmetry; pattern a at 1; rewrite H5; pattern b at 1; rewrite H3; ring).
  assert (c * (a / c - b / c) >= c * 1).
  apply Zmult_ge_compat_l.
  omega.
  omega.
  assert (c * 1 = c).
  ring.
  omega.
Qed.

Lemma ZO_div_monotone : forall a b c, 0<=c -> a<=b -> a/c <= b/c.
Proof.
  intros.
  destruct (Z_le_gt_dec 0 a).
  apply ZO_div_monotone_pos; auto with zarith.
  destruct (Z_le_gt_dec 0 b).
  apply Zle_trans with 0.
  apply Zle_left_rev.
  simpl.
  rewrite <- ZOdiv_opp_l.
  apply ZO_div_pos; auto with zarith.
  apply ZO_div_pos; auto with zarith.
  rewrite <-(Zopp_involutive a), (ZOdiv_opp_l (-a)).
  rewrite <-(Zopp_involutive b), (ZOdiv_opp_l (-b)).
  generalize (ZO_div_monotone_pos (-b) (-a) c H).
  romega.
Qed.

(** With our choice of division, rounding of (a/b) is always done toward zero: *)

Lemma ZO_mult_div_le : forall a b:Z, 0 <= a -> 0 <= b*(a/b) <= a.
Proof.
  intros a b Ha.
  destruct b as [ |b|b].
  simpl; auto with zarith.
  split.
  apply Zmult_le_0_compat; auto with zarith.
  apply ZO_div_pos; auto with zarith.
  generalize (ZO_div_mod_eq a (Zpos b)) (ZOmod_lt_pos_pos a (Zpos b) Ha); romega with *.
  change (Zneg b) with (-Zpos b); rewrite ZOdiv_opp_r, Zmult_opp_opp.
  split.
  apply Zmult_le_0_compat; auto with zarith.
  apply ZO_div_pos; auto with zarith.
  generalize (ZO_div_mod_eq a (Zpos b)) (ZOmod_lt_pos_pos a (Zpos b) Ha); romega with *.
Qed.

Lemma ZO_mult_div_ge : forall a b:Z, a <= 0 -> a <= b*(a/b) <= 0.
Proof.
  intros a b Ha.
  destruct b as [ |b|b].
  simpl; auto with zarith.
  split.
  generalize (ZO_div_mod_eq a (Zpos b)) (ZOmod_lt_neg_pos a (Zpos b) Ha); romega with *.
  apply Zle_left_rev; unfold Zplus.
  rewrite Zopp_mult_distr_r, <-ZOdiv_opp_l.
  apply Zmult_le_0_compat; auto with zarith.
  apply ZO_div_pos; auto with zarith.
  change (Zneg b) with (-Zpos b); rewrite ZOdiv_opp_r, Zmult_opp_opp.
  split.
  generalize (ZO_div_mod_eq a (Zpos b)) (ZOmod_lt_neg_pos a (Zpos b) Ha); romega with *.
  apply Zle_left_rev; unfold Zplus.
  rewrite Zopp_mult_distr_r, <-ZOdiv_opp_l.
  apply Zmult_le_0_compat; auto with zarith.
  apply ZO_div_pos; auto with zarith.
Qed.

(** The previous inequalities between [b*(a/b)] and [a] are exact 
    iff the modulo is zero. *)

Lemma ZO_div_exact_full_1 : forall a b:Z, a = b*(a/b) -> a mod b = 0.
Proof.
  intros; generalize (ZO_div_mod_eq a b); romega.
Qed.

Lemma ZO_div_exact_full_2 : forall a b:Z, a mod b = 0 -> a = b*(a/b).
Proof.
  intros; generalize (ZO_div_mod_eq a b); romega.
Qed.

(** A modulo cannot grow beyond its starting point. *)

Theorem ZOmod_le: forall a b, 0 <= a -> 0 <= b -> a mod b <= a.
Proof. 
  intros a b H1 H2.
  destruct (Zle_lt_or_eq _ _ H2).
  case (Zle_or_lt b a); intros H3.
  case (ZOmod_lt_pos_pos a b); auto with zarith.
  rewrite ZOmod_small; auto with zarith.
  subst; rewrite ZOmod_0_r; auto with zarith.
Qed.

(** Some additionnal inequalities about Zdiv. *)

Theorem ZOdiv_le_upper_bound: 
  forall a b q, 0 <= a -> 0 < b -> a <= q*b -> a/b <= q.
Proof.
  intros a b q H1 H2 H3.
  apply Zmult_le_reg_r with b; auto with zarith.
  apply Zle_trans with (2 := H3).
  pattern a at 2; rewrite (ZO_div_mod_eq a b); auto with zarith.
  rewrite (Zmult_comm b); case (ZOmod_lt_pos_pos a b); auto with zarith.
Qed.

Theorem ZOdiv_lt_upper_bound: 
  forall a b q, 0 <= a -> 0 < b -> a < q*b -> a/b < q.
Proof.
  intros a b q H1 H2 H3.
  apply Zmult_lt_reg_r with b; auto with zarith.
  apply Zle_lt_trans with (2 := H3).
  pattern a at 2; rewrite (ZO_div_mod_eq a b); auto with zarith.
  rewrite (Zmult_comm b); case (ZOmod_lt_pos_pos a b); auto with zarith.
Qed.

Theorem ZOdiv_le_lower_bound: 
  forall a b q, 0 <= a -> 0 < b -> q*b <= a -> q <= a/b.
Proof.
  intros a b q H1 H2 H3.
  assert (q < a / b + 1); auto with zarith.
  apply Zmult_lt_reg_r with b; auto with zarith.
  apply Zle_lt_trans with (1 := H3).
  pattern a at 1; rewrite (ZO_div_mod_eq a b); auto with zarith.
  rewrite Zmult_plus_distr_l; rewrite (Zmult_comm b); case (ZOmod_lt_pos_pos a b);
   auto with zarith.
Qed.

Theorem ZOdiv_sgn: forall a b, 
  0 <= Zsgn (a/b) * Zsgn a * Zsgn b.
Proof.
  destruct a as [ |a|a]; destruct b as [ |b|b]; simpl; auto with zarith; 
  unfold ZOdiv; simpl; destruct Pdiv_eucl; simpl; destruct n; simpl; auto with zarith.
Qed.

(** * Relations between usual operations and Zmod and Zdiv *)

(** First, a result that used to be always valid with Zdiv, 
    but must be restricted here. 
    For instance, now (9+(-5)*2) mod 2 = -1 <> 1 = 9 mod 2 *)

Lemma ZO_mod_plus : forall a b c:Z, 
 0 <= (a+b*c) * a -> 
 (a + b * c) mod c = a mod c.
Proof.
  intros; destruct (Z_eq_dec a 0) as [Ha|Ha].
  subst; simpl; rewrite ZOmod_0_l; apply ZO_mod_mult.
  intros; destruct (Z_eq_dec c 0) as [Hc|Hc].
  subst; do 2 rewrite ZOmod_0_r; romega.
  symmetry; apply ZOmod_unique_full with (a/c+b); auto with zarith.
  rewrite Remainder_equiv; split.
  apply ZOmod_lt; auto.
  apply Zmult_le_0_reg_r with (a*a); eauto.
  destruct a; simpl; auto with zarith.
  replace ((a mod c)*(a+b*c)*(a*a)) with (((a mod c)*a)*((a+b*c)*a)) by ring.
  apply Zmult_le_0_compat; auto.
  apply ZOmod_sgn2.
  rewrite Zmult_plus_distr_r, Zmult_comm.
  generalize (ZO_div_mod_eq a c); romega.
Qed.

Lemma ZO_div_plus : forall a b c:Z, 
 0 <= (a+b*c) * a -> c<>0 -> 
 (a + b * c) / c = a / c + b.
Proof.
  intros; destruct (Z_eq_dec a 0) as [Ha|Ha].
  subst; simpl; apply ZO_div_mult; auto.
  symmetry.
  apply ZOdiv_unique_full with (a mod c); auto with zarith.
  rewrite Remainder_equiv; split.
  apply ZOmod_lt; auto.
  apply Zmult_le_0_reg_r with (a*a); eauto.
  destruct a; simpl; auto with zarith.
  replace ((a mod c)*(a+b*c)*(a*a)) with (((a mod c)*a)*((a+b*c)*a)) by ring.
  apply Zmult_le_0_compat; auto.
  apply ZOmod_sgn2.
  rewrite Zmult_plus_distr_r, Zmult_comm.
  generalize (ZO_div_mod_eq a c); romega.
Qed.

Theorem ZO_div_plus_l: forall a b c : Z, 
 0 <= (a*b+c)*c -> b<>0 -> 
 b<>0 -> (a * b + c) / b = a + c / b.
Proof.
  intros a b c; rewrite Zplus_comm; intros; rewrite ZO_div_plus;
  try apply Zplus_comm; auto with zarith. 
Qed.

(** Cancellations. *)

Lemma ZOdiv_mult_cancel_r : forall a b c:Z, 
 c<>0 -> (a*c)/(b*c) = a/b.
Proof.
 intros a b c Hc.
 destruct (Z_eq_dec b 0).
 subst; simpl; do 2 rewrite ZOdiv_0_r; auto.
 symmetry.
 apply ZOdiv_unique_full with ((a mod b)*c); auto with zarith.
 rewrite Remainder_equiv.
 split.
 do 2 rewrite Zabs_Zmult.
 apply Zmult_lt_compat_r.
 romega with *.
 apply ZOmod_lt; auto.
 replace ((a mod b)*c*(a*c)) with (((a mod b)*a)*(c*c)) by ring.
 apply Zmult_le_0_compat.
 apply ZOmod_sgn2.
 destruct c; simpl; auto with zarith.
 pattern a at 1; rewrite (ZO_div_mod_eq a b); ring.
Qed.

Lemma ZOdiv_mult_cancel_l : forall a b c:Z, 
 c<>0 -> (c*a)/(c*b) = a/b.
Proof.
  intros.
  rewrite (Zmult_comm c a); rewrite (Zmult_comm c b).
  apply ZOdiv_mult_cancel_r; auto.
Qed.

Lemma ZOmult_mod_distr_l: forall a b c, 
  (c*a) mod (c*b) = c * (a mod b).
Proof.
  intros; destruct (Z_eq_dec c 0) as [Hc|Hc].
  subst; simpl; rewrite ZOmod_0_r; auto.
  destruct (Z_eq_dec b 0) as [Hb|Hb].
  subst; repeat rewrite Zmult_0_r || rewrite ZOmod_0_r; auto.
  assert (c*b <> 0).
   contradict Hc; eapply Zmult_integral_l; eauto.
  rewrite (Zplus_minus_eq _ _ _ (ZO_div_mod_eq (c*a) (c*b))).
  rewrite (Zplus_minus_eq _ _ _ (ZO_div_mod_eq a b)).
  rewrite ZOdiv_mult_cancel_l; auto with zarith.
  ring.
Qed.

Lemma ZOmult_mod_distr_r: forall a b c, 
  (a*c) mod (b*c) = (a mod b) * c.
Proof.
  intros; repeat rewrite (fun x => (Zmult_comm x c)).
  apply ZOmult_mod_distr_l; auto.
Qed.

(** Operations modulo. *)

Theorem ZOmod_mod: forall a n, (a mod n) mod n = a mod n.
Proof.
  intros.
  generalize (ZOmod_sgn2 a n).
  pattern a at 2 4; rewrite (ZO_div_mod_eq a n); auto with zarith.
  rewrite Zplus_comm; rewrite (Zmult_comm n).
  intros.
  apply sym_equal; apply ZO_mod_plus; auto with zarith.
  rewrite Zmult_comm; auto.
Qed.

Theorem ZOmult_mod: forall a b n,
 (a * b) mod n = ((a mod n) * (b mod n)) mod n.
Proof.
  intros.
  generalize (Zmult_le_0_compat _ _ (ZOmod_sgn2 a n) (ZOmod_sgn2 b n)).
  pattern a at 2 3; rewrite (ZO_div_mod_eq a n); auto with zarith.
  pattern b at 2 3; rewrite (ZO_div_mod_eq b n); auto with zarith.
  set (A:=a mod n); set (B:=b mod n); set (A':=a/n); set (B':=b/n).
  replace (A*(n*A'+A)*(B*(n*B'+B))) with (((n*A' + A) * (n*B' + B))*(A*B)) 
   by ring.
  replace ((n*A' + A) * (n*B' + B))
   with (A*B + (A'*B+B'*A+n*A'*B')*n) by ring.
  intros.
  apply ZO_mod_plus; auto with zarith.
Qed.

(** addition and modulo
  
  Generally speaking, unlike with Zdiv, we don't have 
       (a+b) mod n = (a mod n + b mod n) mod n 
  for any a and b. 
  For instance, take (8 + (-10)) mod 3 = -2 whereas 
  (8 mod 3 + (-10 mod 3)) mod 3 = 1. *)

Theorem ZOplus_mod: forall a b n,
 0 <= a * b -> 
 (a + b) mod n = (a mod n + b mod n) mod n.
Proof.
  assert (forall a b n, 0<a -> 0<b ->
           (a + b) mod n = (a mod n + b mod n) mod n).
  intros a b n Ha Hb.
  assert (H : 0<=a+b) by (romega with * ); revert H.
  pattern a at 1 2; rewrite (ZO_div_mod_eq a n); auto with zarith.
  pattern b at 1 2; rewrite (ZO_div_mod_eq b n); auto with zarith.
  replace ((n * (a / n) + a mod n) + (n * (b / n) + b mod n))
     with ((a mod n + b mod n) + (a / n + b / n) * n) by ring.
  intros.
  apply ZO_mod_plus; auto with zarith.
  apply Zmult_le_0_compat; auto with zarith.
  apply Zplus_le_0_compat.
  apply Zmult_le_reg_r with a; auto with zarith.
  simpl; apply ZOmod_sgn2; auto.
  apply Zmult_le_reg_r with b; auto with zarith.
  simpl; apply ZOmod_sgn2; auto.
  (* general situation *)
  intros a b n Hab.
  destruct (Z_eq_dec a 0).
  subst; simpl; symmetry; apply ZOmod_mod.
  destruct (Z_eq_dec b 0).
  subst; simpl; do 2 rewrite Zplus_0_r; symmetry; apply ZOmod_mod.
  assert (0<a /\ 0<b \/ a<0 /\ b<0).
   destruct a; destruct b; simpl in *; intuition; romega with *.
  destruct H0.
  apply H; intuition.
  rewrite <-(Zopp_involutive a), <-(Zopp_involutive b).
  rewrite <- Zopp_plus_distr; rewrite ZOmod_opp_l.
  rewrite (ZOmod_opp_l (-a)),(ZOmod_opp_l (-b)).
  match goal with |- _ = (-?x+-?y) mod n => 
   rewrite <-(Zopp_plus_distr x y), ZOmod_opp_l end.
  f_equal; apply H; auto with zarith.
Qed.

Lemma ZOplus_mod_idemp_l: forall a b n, 
 0 <= a * b -> 
 (a mod n + b) mod n = (a + b) mod n.
Proof.
  intros. 
  rewrite ZOplus_mod.
  rewrite ZOmod_mod.
  symmetry.
  apply ZOplus_mod; auto.
  destruct (Z_eq_dec a 0).
  subst; rewrite ZOmod_0_l; auto.
  destruct (Z_eq_dec b 0).
  subst; rewrite Zmult_0_r; auto with zarith.
  apply Zmult_le_reg_r with (a*b).
  assert (a*b <> 0).
   intro Hab.
   rewrite (Zmult_integral_l _ _ n1 Hab) in n0; auto with zarith.
  auto with zarith.
  simpl.
  replace (a mod n * b * (a*b)) with ((a mod n * a)*(b*b)) by ring.
  apply Zmult_le_0_compat.
  apply ZOmod_sgn2.
  destruct b; simpl; auto with zarith.
Qed.

Lemma ZOplus_mod_idemp_r: forall a b n, 
 0 <= a*b -> 
 (b + a mod n) mod n = (b + a) mod n.
Proof.
  intros.
  rewrite Zplus_comm, (Zplus_comm b a).
  apply ZOplus_mod_idemp_l; auto.
Qed.

Lemma ZOmult_mod_idemp_l: forall a b n, (a mod n * b) mod n = (a * b) mod n.
Proof.
  intros; rewrite ZOmult_mod, ZOmod_mod, <- ZOmult_mod; auto.
Qed.

Lemma ZOmult_mod_idemp_r: forall a b n, (b * (a mod n)) mod n = (b * a) mod n.
Proof.
  intros; rewrite ZOmult_mod, ZOmod_mod, <- ZOmult_mod; auto.
Qed.

(** Unlike with Zdiv, the following result is true without restrictions. *)

Lemma ZOdiv_ZOdiv : forall a b c, (a/b)/c = a/(b*c).
Proof.
  (* particular case: a, b, c positive *)
  assert (forall a b c, a>0 -> b>0 -> c>0 -> (a/b)/c = a/(b*c)).
   intros a b c H H0 H1.
   pattern a at 2;rewrite (ZO_div_mod_eq a b).
   pattern (a/b) at 2;rewrite (ZO_div_mod_eq (a/b) c).
   replace (b * (c * (a / b / c) + (a / b) mod c) + a mod b) with
    ((a / b / c)*(b * c)  + (b * ((a / b) mod c) + a mod b)) by ring.
   assert (b*c<>0).
    intro H2; 
    assert (H3: c <> 0) by auto with zarith; 
    rewrite (Zmult_integral_l _ _ H3 H2) in H0; auto with zarith.
   assert (0<=a/b) by (apply (ZO_div_pos a b); auto with zarith).
   assert (0<=a mod b < b) by (apply ZOmod_lt_pos_pos; auto with zarith).
   assert (0<=(a/b) mod c < c) by 
    (apply ZOmod_lt_pos_pos; auto with zarith).
   rewrite ZO_div_plus_l; auto with zarith.
   rewrite (ZOdiv_small (b * ((a / b) mod c) + a mod b)).
   ring.
   split.
   apply Zplus_le_0_compat;auto with zarith.
   apply Zle_lt_trans with (b * ((a / b) mod c) + (b-1)).
   apply Zplus_le_compat;auto with zarith.
   apply Zle_lt_trans with (b * (c-1) + (b - 1)).
   apply Zplus_le_compat;auto with zarith.
   replace (b * (c - 1) + (b - 1)) with (b*c-1);try ring;auto with zarith.
   repeat (apply Zmult_le_0_compat || apply Zplus_le_0_compat); auto with zarith.
   apply (ZO_div_pos (a/b) c); auto with zarith.
  (* b c positive, a general *)
  assert (forall a b c, b>0 -> c>0 -> (a/b)/c = a/(b*c)).
   intros; destruct a as [ |a|a]; try reflexivity.
   apply H; auto with zarith.
   change (Zneg a) with (-Zpos a); repeat rewrite ZOdiv_opp_l.
   f_equal; apply H; auto with zarith.
  (* c positive, a b general *)
  assert (forall a b c, c>0 -> (a/b)/c = a/(b*c)).
   intros; destruct b as [ |b|b].
   repeat rewrite ZOdiv_0_r; reflexivity.
   apply H0; auto with zarith.
   change (Zneg b) with (-Zpos b); 
   repeat (rewrite ZOdiv_opp_r || rewrite ZOdiv_opp_l || rewrite <- Zopp_mult_distr_l).
   f_equal; apply H0; auto with zarith.
  (* a b c general *)
  intros; destruct c as [ |c|c].
  rewrite Zmult_0_r; repeat rewrite ZOdiv_0_r; reflexivity.
  apply H1; auto with zarith.
  change (Zneg c) with (-Zpos c); 
  rewrite <- Zopp_mult_distr_r; do 2 rewrite ZOdiv_opp_r.
  f_equal; apply H1; auto with zarith.
Qed.

(** A last inequality: *)

Theorem ZOdiv_mult_le:
 forall a b c, 0<=a -> 0<=b -> 0<=c -> c*(a/b) <= (c*a)/b.
Proof.
  intros a b c Ha Hb Hc.
  destruct (Zle_lt_or_eq _ _ Ha); 
   [ | subst; rewrite ZOdiv_0_l, Zmult_0_r, ZOdiv_0_l; auto].
  destruct (Zle_lt_or_eq _ _ Hb); 
   [ | subst; rewrite ZOdiv_0_r, ZOdiv_0_r, Zmult_0_r; auto].
  destruct (Zle_lt_or_eq _ _ Hc); 
   [ | subst; rewrite ZOdiv_0_l; auto].
  case (ZOmod_lt_pos_pos a b); auto with zarith; intros Hu1 Hu2.
  case (ZOmod_lt_pos_pos c b); auto with zarith; intros Hv1 Hv2.
  apply Zmult_le_reg_r with b; auto with zarith.
  rewrite <- Zmult_assoc.
  replace (a / b * b) with (a - a mod b).
  replace (c * a / b * b) with (c * a - (c * a) mod b).
  rewrite Zmult_minus_distr_l.
  unfold Zminus; apply Zplus_le_compat_l.
  match goal with |- - ?X <= -?Y => assert (Y <= X); auto with zarith end.
  apply Zle_trans with ((c mod b) * (a mod b)); auto with zarith.
  rewrite ZOmult_mod; auto with zarith.
  apply (ZOmod_le ((c mod b) * (a mod b)) b); auto with zarith.
  apply Zmult_le_compat_r; auto with zarith.
  apply (ZOmod_le c b); auto.
  pattern (c * a) at 1; rewrite (ZO_div_mod_eq (c * a) b); try ring; 
    auto with zarith.
  pattern a at 1; rewrite (ZO_div_mod_eq a b); try ring; auto with zarith.
Qed.

(** ZOmod is related to divisibility (see more in Znumtheory) *)

Lemma ZOmod_divides : forall a b, 
 a mod b = 0 <-> exists c, a = b*c.
Proof.
 split; intros.
 exists (a/b).
 pattern a at 1; rewrite (ZO_div_mod_eq a b).
 rewrite H; auto with zarith.
 destruct H as [c Hc].
 destruct (Z_eq_dec b 0).
 subst b; simpl in *; subst a; auto.
 symmetry.
 apply ZOmod_unique_full with c; auto with zarith.
 red; romega with *.
Qed.

(** * Interaction with "historic" Zdiv *)

(** They agree at least on positive numbers: *)

Theorem ZOdiv_eucl_Zdiv_eucl_pos : forall a b:Z, 0 <= a -> 0 < b -> 
  a/b = Zdiv.Zdiv a b /\ a mod b = Zdiv.Zmod a b.
Proof.
  intros.
  apply Zdiv.Zdiv_mod_unique with b.
  apply ZOmod_lt_pos; auto with zarith.
  rewrite Zabs_eq; auto with *; apply Zdiv.Z_mod_lt; auto with *.
  rewrite <- Zdiv.Z_div_mod_eq; auto with *.
  symmetry; apply ZO_div_mod_eq; auto with *.
Qed.

Theorem ZOdiv_Zdiv_pos : forall a b, 0 <= a -> 0 <= b -> 
  a/b = Zdiv.Zdiv a b.
Proof.
 intros a b Ha Hb.
 destruct (Zle_lt_or_eq _ _ Hb).
 generalize (ZOdiv_eucl_Zdiv_eucl_pos a b Ha H); intuition.
 subst; rewrite ZOdiv_0_r, Zdiv.Zdiv_0_r; reflexivity.
Qed.

Theorem ZOmod_Zmod_pos : forall a b, 0 <= a -> 0 < b -> 
  a mod b = Zdiv.Zmod a b.
Proof.
 intros a b Ha Hb; generalize (ZOdiv_eucl_Zdiv_eucl_pos a b Ha Hb);
 intuition.
Qed.

(** Modulos are null at the same places *)

Theorem ZOmod_Zmod_zero : forall a b, b<>0 -> 
 (a mod b = 0 <-> Zdiv.Zmod a b = 0).
Proof.
 intros.
 rewrite ZOmod_divides, Zdiv.Zmod_divides; intuition.
Qed. 
