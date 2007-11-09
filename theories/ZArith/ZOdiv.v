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

(** Reformulation of the last two general statements in 2 
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
  Zabs r < Zabs b /\ 0 <= Zsgn r * Zsgn a.

Lemma Remainder_equiv : forall a b r, 
 Remainder a b r <-> Remainder_alt a b r.
Proof.
  unfold Remainder, Remainder_alt; intuition.
  romega with *.
  destruct (Zle_lt_or_eq _ _ H).
  rewrite <- Zsgn_pos in H1; rewrite H1.
  romega with *.
  subst; simpl; romega.
  rewrite Zabs_non_eq; auto with *.
  destruct (Zle_lt_or_eq _ _ H).
  rewrite <- Zsgn_neg in H1; rewrite H1.
  romega with *.
  subst; simpl; romega.
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

Lemma ZO_div_pos_monotone : forall a b c:Z, 0<=c -> 0 <= a <= b -> a/c <= b/c.
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

Lemma ZO_div_monotone : forall a b c, 0 <= c -> a <= b -> a/c <= b/c.
Proof.
  intros.
  destruct (Z_le_gt_dec 0 a).
  apply ZO_div_pos_monotone; auto with zarith.
  destruct (Z_le_gt_dec 0 b).
  apply Zle_trans with 0.
  apply Zle_left_rev.
  simpl.
  rewrite <- ZOdiv_opp_l.
  apply ZO_div_pos; auto with zarith.
  apply ZO_div_pos; auto with zarith.
  rewrite <-(Zopp_involutive a), (ZOdiv_opp_l (-a)).
  rewrite <-(Zopp_involutive b), (ZOdiv_opp_l (-b)).
  generalize (ZO_div_pos_monotone (-b) (-a) c H).
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

(* NOT FINISHED YET ...

(** * Relations between usual operations and Zmod and Zdiv *)

Eval compute in ((10-4*3) mod 3).

Lemma ZO_mod_plus : forall a b c:Z, (a + b * c) mod c = a mod c. (*FAUX*)
Proof.
  intros; destruct (Z_eq_dec c 0) as [Hc|Hc].
  subst; do 2 rewrite ZOmod_0_r; romega.
  symmetry; apply ZOmod_unique_full with (a/c+b); auto with zarith.
  rewrite Remainder_equiv; split.
  apply ZOmod_lt; auto.
  generalize (ZOmod_sgn a c); intros.
   admit.
  rewrite Zmult_plus_distr_r, Zmult_comm.
  generalize (ZO_div_mod_eq a c); romega.
Qed.

Lemma ZO_div_plus : forall a b c:Z, c<>0 -> (a + b * c) / c = a / c + b.
Proof.
  intro; symmetry.
  apply ZOdiv_unique_full with (a mod c); auto with zarith.
  rewrite Remainder_equiv; split.
  apply ZOmod_lt; auto.
  generalize (ZOmod_sgn a c); intros.
   admit.
  rewrite Zmult_plus_distr_r, Zmult_comm.
  generalize (ZO_div_mod_eq a c); romega.
Qed.

Theorem ZO_div_plus_l: forall a b c : Z, b <> 0 -> (a * b + c) / b = a + c / b.
Proof.
  intros a b c H; rewrite Zplus_comm; rewrite ZO_div_plus;
  try apply Zplus_comm; auto with zarith. 
Qed.

(** Cancellations. *)

Lemma Zdiv_mult_cancel_r : forall a b c:Z, 
 c <> 0 -> (a*c)/(b*c) = a/b.
Proof.
assert (X: forall a b c, b > 0 -> c > 0 -> (a*c) / (b*c) = a / b).
 intros a b c Hb Hc.
 symmetry.
 apply Zdiv_unique with ((a mod b)*c); auto with zarith.
 destruct (Z_mod_lt a b Hb); split.
 apply Zmult_le_0_compat; auto with zarith.
 apply Zmult_lt_compat_r; auto with zarith.
 pattern a at 1; rewrite (Z_div_mod_eq a b Hb); ring.
intros a b c Hc.
destruct (Z_dec b 0) as [Hb|Hb]. 
destruct Hb as [Hb|Hb]; destruct (not_Zeq_inf _ _ Hc); auto with *.
rewrite <- (Zdiv_opp_opp a), <- (Zmult_opp_opp b), <-(Zmult_opp_opp a); 
 auto with *.
rewrite <- (Zdiv_opp_opp a), <- Zdiv_opp_opp, Zopp_mult_distr_l, 
 Zopp_mult_distr_l; auto with *.
rewrite <- Zdiv_opp_opp, Zopp_mult_distr_r, Zopp_mult_distr_r; auto with *.
rewrite Hb; simpl; do 2 rewrite Zdiv_0_r; auto.
Qed.

Lemma Zdiv_mult_cancel_l : forall a b c:Z, 
 c<>0 -> (c*a)/(c*b) = a/b.
Proof.
  intros.
  rewrite (Zmult_comm c a); rewrite (Zmult_comm c b).
  apply Zdiv_mult_cancel_r; auto.
Qed.

Lemma Zmult_mod_distr_l: forall a b c, 
  (c*a) mod (c*b) = c * (a mod b).
Proof.
  intros; destruct (Z_eq_dec c 0) as [Hc|Hc].
  subst; simpl; rewrite Zmod_0_r; auto.
  destruct (Z_eq_dec b 0) as [Hb|Hb].
  subst; repeat rewrite Zmult_0_r || rewrite Zmod_0_r; auto.
  assert (c*b <> 0).
   contradict Hc; eapply Zmult_integral_l; eauto.
  rewrite (Zplus_minus_eq _ _ _ (Z_div_mod_eq_full (c*a) (c*b) H)).
  rewrite (Zplus_minus_eq _ _ _ (Z_div_mod_eq_full a b Hb)).
  rewrite Zdiv_mult_cancel_l; auto with zarith.
  ring.
Qed.

Lemma Zmult_mod_distr_r: forall a b c, 
  (a*c) mod (b*c) = (a mod b) * c.
Proof.
  intros; repeat rewrite (fun x => (Zmult_comm x c)).
  apply Zmult_mod_distr_l; auto.
Qed.

(** Operations modulo. *)

Theorem Zmod_mod: forall a n, (a mod n) mod n = a mod n.
Proof.
  intros; destruct (Z_eq_dec n 0) as [Hb|Hb].
  subst; do 2 rewrite Zmod_0_r; auto.
  pattern a at 2; rewrite (Z_div_mod_eq_full a n); auto with zarith.
  rewrite Zplus_comm; rewrite Zmult_comm.
  apply sym_equal; apply Z_mod_plus_full; auto with zarith.
Qed.

Theorem Zmult_mod: forall a b n,
 (a * b) mod n = ((a mod n) * (b mod n)) mod n.
Proof.
  intros; destruct (Z_eq_dec n 0) as [Hb|Hb].
  subst; do 2 rewrite Zmod_0_r; auto.
  pattern a at 1; rewrite (Z_div_mod_eq_full a n); auto with zarith.
  pattern b at 1; rewrite (Z_div_mod_eq_full b n); auto with zarith.
  set (A:=a mod n); set (B:=b mod n); set (A':=a/n); set (B':=b/n).
  replace ((n*A' + A) * (n*B' + B))
   with (A*B + (A'*B+B'*A+n*A'*B')*n) by ring.
  apply Z_mod_plus_full; auto with zarith.
Qed.

Theorem Zplus_mod: forall a b n,
 (a + b) mod n = (a mod n + b mod n) mod n.
Proof.
  intros; destruct (Z_eq_dec n 0) as [Hb|Hb].
  subst; do 2 rewrite Zmod_0_r; auto.
  pattern a at 1; rewrite (Z_div_mod_eq_full a n); auto with zarith.
  pattern b at 1; rewrite (Z_div_mod_eq_full b n); auto with zarith.
  replace ((n * (a / n) + a mod n) + (n * (b / n) + b mod n))
     with ((a mod n + b mod n) + (a / n + b / n) * n) by ring.
  apply Z_mod_plus_full; auto with zarith.
Qed.

Theorem Zminus_mod: forall a b n,
 (a - b) mod n = (a mod n - b mod n) mod n.
Proof.
  intros.
  replace (a - b) with (a + (-1) * b); auto with zarith.
  replace (a mod n - b mod n) with (a mod n + (-1) * (b mod n)); auto with zarith.
  rewrite Zplus_mod.
  rewrite Zmult_mod.
  rewrite Zplus_mod with (b:=(-1) * (b mod n)).
  rewrite Zmult_mod.
  rewrite Zmult_mod with (b:= b mod n).
  repeat rewrite Zmod_mod; auto.
Qed.

Lemma Zplus_mod_idemp_l: forall a b n, (a mod n + b) mod n = (a + b) mod n.
Proof.
  intros; rewrite Zplus_mod, Zmod_mod, <- Zplus_mod; auto.
Qed.

Lemma Zplus_mod_idemp_r: forall a b n, (b + a mod n) mod n = (b + a) mod n.
Proof.
  intros; rewrite Zplus_mod, Zmod_mod, <- Zplus_mod; auto.
Qed.

Lemma Zminus_mod_idemp_l: forall a b n, (a mod n - b) mod n = (a - b) mod n.
Proof.
  intros; rewrite Zminus_mod, Zmod_mod, <- Zminus_mod; auto.
Qed.

Lemma Zminus_mod_idemp_r: forall a b n, (a - b mod n) mod n = (a - b) mod n.
Proof.
  intros; rewrite Zminus_mod, Zmod_mod, <- Zminus_mod; auto.
Qed.

Lemma Zmult_mod_idemp_l: forall a b n, (a mod n * b) mod n = (a * b) mod n.
Proof.
  intros; rewrite Zmult_mod, Zmod_mod, <- Zmult_mod; auto.
Qed.

Lemma Zmult_mod_idemp_r: forall a b n, (b * (a mod n)) mod n = (b * a) mod n.
Proof.
  intros; rewrite Zmult_mod, Zmod_mod, <- Zmult_mod; auto.
Qed.

Lemma Zdiv_Zdiv : forall a b c, b>0 -> c>0 -> (a/b)/c = a/(b*c).
Proof.
  intros a b c H H0.
  pattern a at 2;rewrite (Z_div_mod_eq_full a b);auto with zarith.
  pattern (a/b) at 2;rewrite (Z_div_mod_eq_full (a/b) c);auto with zarith.
  replace (b * (c * (a / b / c) + (a / b) mod c) + a mod b) with
    ((a / b / c)*(b * c)  + (b * ((a / b) mod c) + a mod b)) by ring.
  rewrite Z_div_plus_full_l; auto with zarith.
  rewrite (Zdiv_small (b * ((a / b) mod c) + a mod b)).
  ring.
  split.
  apply Zplus_le_0_compat;auto with zarith.
  apply Zmult_le_0_compat;auto with zarith.
  destruct (Z_mod_lt (a/b) c);auto with zarith.
  destruct (Z_mod_lt a b);auto with zarith.
  apply Zle_lt_trans with (b * ((a / b) mod c) + (b-1)).
  destruct (Z_mod_lt a b);auto with zarith.
  apply Zle_lt_trans with (b * (c-1) + (b - 1)).
  apply Zplus_le_compat;auto with zarith.
  destruct (Z_mod_lt (a/b) c);auto with zarith.
  replace (b * (c - 1) + (b - 1)) with (b*c-1);try ring;auto with zarith.
  intro H1; 
  assert (H2: c <> 0) by auto with zarith; 
  rewrite (Zmult_integral_l _ _ H2 H1) in H; auto with zarith.
Qed.

(** Unfortunately, the previous result isn't always true on negative numbers.
    For instance: 3/(-2)/(-2) = 1 <> 0 = 3 / (-2*-2) *)

(** A last inequality: *)

Theorem Zdiv_mult_le:
 forall a b c, 0 <= a -> 0 < b -> 0 <= c -> c*(a/b) <= (c*a)/b.
Proof.
  intros a b c H1 H2 H3.
  case (Z_mod_lt a b); auto with zarith; intros Hu1 Hu2.
  case (Z_mod_lt c b); auto with zarith; intros Hv1 Hv2.
  apply Zmult_le_reg_r with b; auto with zarith.
  rewrite <- Zmult_assoc.
  replace (a / b * b) with (a - a mod b).
  replace (c * a / b * b) with (c * a - (c * a) mod b).
  rewrite Zmult_minus_distr_l.
  unfold Zminus; apply Zplus_le_compat_l.
  match goal with |- - ?X <= -?Y => assert (Y <= X); auto with zarith end.
  apply Zle_trans with ((c mod b) * (a mod b)); auto with zarith.
  rewrite Zmult_mod; auto with zarith.
  apply (Zmod_le ((c mod b) * (a mod b)) b); auto with zarith.
  apply Zmult_le_compat_r; auto with zarith.
  apply (Zmod_le c b); auto.
  pattern (c * a) at 1; rewrite (Z_div_mod_eq (c * a) b); try ring; 
    auto with zarith.
  pattern a at 1; rewrite (Z_div_mod_eq a b); try ring; auto with zarith.
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

Theorem ZOdiv_Zdiv_pos : forall a b, 0 <= a -> 0 < b -> 
  a/b = Zdiv.Zdiv a b.
Proof.
 intros a b Ha Hb; generalize (ZOdiv_eucl_Zdiv_eucl_pos a b Ha Hb); 
 intuition.
Qed.  

Theorem ZOmod_Zmod_pos : forall a b, 0 <= a -> 0 < b -> 
  a mod b = Zdiv.Zmod a b.
Proof.
 intros a b Ha Hb; generalize (ZOdiv_eucl_Zdiv_eucl_pos a b Ha Hb);
 intuition.
Qed.

(*  NOT FINISHED YET !!

(** Modulo are null at the same places *)

Theorem ZOmod_Zmod_zero : forall a b, b<>0 -> 
 a mod b = 0 <-> Zdiv.Zmod a b = 0.

*)
