(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


Require Import BinPos BinNat Nnat ZArith_base ROmega ZArithRing
 ZBinary ZDivTrunc Morphisms.
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

(** We know enough to prove that [ZOdiv] and [ZOmod] are instances of
    one of the abstract Euclidean divisions of Numbers. *)

Module ZODiv <: ZDiv ZBinAxiomsMod.
 Definition div := ZOdiv.
 Definition modulo := ZOmod.
 Program Instance div_wd : Proper (eq==>eq==>eq) div.
 Program Instance mod_wd : Proper (eq==>eq==>eq) modulo.

 Definition div_mod := fun a b (_:b<>0) => ZO_div_mod_eq a b.
 Definition mod_bound := ZOmod_lt_pos_pos.
 Definition mod_opp_l := fun a b (_:b<>0) => ZOmod_opp_l a b.
 Definition mod_opp_r := fun a b (_:b<>0) => ZOmod_opp_r a b.
End ZODiv.

Module ZODivMod := ZBinAxiomsMod <+ ZODiv.

(** We hence benefit from generic results about this abstract division. *)

Module Z.
 Include ZDivPropFunct ZODivMod.
End Z.

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
Proof. exact Z.div_unique. Qed.

Theorem ZOmod_unique_full:
 forall a b q r, Remainder a b r ->
  a = b*q + r -> r = a mod b.
Proof.
 intros; destruct (ZOdiv_mod_unique_full a b q r); auto.
Qed.

Theorem ZOmod_unique:
 forall a b q r, 0 <= a -> 0 <= r < b ->
   a = b*q + r -> r = a mod b.
Proof. exact Z.mod_unique. Qed.

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
Proof. exact Z.mod_1_r. Qed.

Lemma ZOdiv_1_r: forall a, a/1 = a.
Proof. exact Z.div_1_r. Qed.

Hint Resolve ZOmod_0_l ZOmod_0_r ZOdiv_0_l ZOdiv_0_r ZOdiv_1_r ZOmod_1_r
 : zarith.

Lemma ZOdiv_1_l: forall a, 1 < a -> 1/a = 0.
Proof. exact Z.div_1_l. Qed.

Lemma ZOmod_1_l: forall a, 1 < a ->  1 mod a = 1.
Proof. exact Z.mod_1_l. Qed.

Lemma ZO_div_same : forall a:Z, a<>0 -> a/a = 1.
Proof. exact Z.div_same. Qed.

Ltac zero_or_not a :=
  destruct (Z_eq_dec a 0);
  [subst; rewrite ?ZOmod_0_l, ?ZOdiv_0_l, ?ZOmod_0_r, ?ZOdiv_0_r;
   auto with zarith|].

Lemma ZO_mod_same : forall a, a mod a = 0.
Proof. intros. zero_or_not a. apply Z.mod_same; auto. Qed.

Lemma ZO_mod_mult : forall a b, (a*b) mod b = 0.
Proof. intros. zero_or_not b. apply Z.mod_mul; auto. Qed.

Lemma ZO_div_mult : forall a b:Z, b <> 0 -> (a*b)/b = a.
Proof. exact Z.div_mul. Qed.

(** * Order results about ZOmod and ZOdiv *)

(* Division of positive numbers is positive. *)

Lemma ZO_div_pos: forall a b, 0 <= a -> 0 <= b -> 0 <= a/b.
Proof. intros. zero_or_not b. apply Z.div_pos; auto with zarith. Qed.

(** As soon as the divisor is greater or equal than 2,
    the division is strictly decreasing. *)

Lemma ZO_div_lt : forall a b:Z, 0 < a -> 2 <= b -> a/b < a.
Proof. intros. apply Z.div_lt; auto with zarith. Qed.

(** A division of a small number by a bigger one yields zero. *)

Theorem ZOdiv_small: forall a b, 0 <= a < b -> a/b = 0.
Proof. exact Z.div_small. Qed.

(** Same situation, in term of modulo: *)

Theorem ZOmod_small: forall a n, 0 <= a < n -> a mod n = a.
Proof. exact Z.mod_small. Qed.

(** [Zge] is compatible with a positive division. *)

Lemma ZO_div_monotone : forall a b c, 0<=c -> a<=b -> a/c <= b/c.
Proof. intros. zero_or_not c. apply Z.div_le_mono; auto with zarith. Qed.

(** With our choice of division, rounding of (a/b) is always done toward zero: *)

Lemma ZO_mult_div_le : forall a b:Z, 0 <= a -> 0 <= b*(a/b) <= a.
Proof. intros. zero_or_not b. apply Z.mul_div_le; auto with zarith. Qed.

Lemma ZO_mult_div_ge : forall a b:Z, a <= 0 -> a <= b*(a/b) <= 0.
Proof. intros. zero_or_not b. apply Z.mul_div_ge; auto with zarith. Qed.

(** The previous inequalities between [b*(a/b)] and [a] are exact
    iff the modulo is zero. *)

Lemma ZO_div_exact_full : forall a b:Z, a = b*(a/b) <-> a mod b = 0.
Proof. intros. zero_or_not b. intuition. apply Z.div_exact; auto. Qed.

(** A modulo cannot grow beyond its starting point. *)

Theorem ZOmod_le: forall a b, 0 <= a -> 0 <= b -> a mod b <= a.
Proof. intros. zero_or_not b. apply Z.mod_le; auto with zarith. Qed.

(** Some additionnal inequalities about Zdiv. *)

Theorem ZOdiv_le_upper_bound:
  forall a b q, 0 < b -> a <= q*b -> a/b <= q.
Proof. intros a b q; rewrite mul_comm; apply Z.div_le_upper_bound. Qed.

Theorem ZOdiv_lt_upper_bound:
  forall a b q, 0 <= a -> 0 < b -> a < q*b -> a/b < q.
Proof. intros a b q; rewrite mul_comm; apply Z.div_lt_upper_bound. Qed.

Theorem ZOdiv_le_lower_bound:
  forall a b q, 0 < b -> q*b <= a -> q <= a/b.
Proof. intros a b q; rewrite mul_comm; apply Z.div_le_lower_bound. Qed.

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
Proof. intros. zero_or_not c. apply Z.mod_add; auto with zarith. Qed.

Lemma ZO_div_plus : forall a b c:Z,
 0 <= (a+b*c) * a -> c<>0 ->
 (a + b * c) / c = a / c + b.
Proof. intros. apply Z.div_add; auto with zarith. Qed.

Theorem ZO_div_plus_l: forall a b c : Z,
 0 <= (a*b+c)*c -> b<>0 ->
 b<>0 -> (a * b + c) / b = a + c / b.
Proof. intros. apply Z.div_add_l; auto with zarith. Qed.

(** Cancellations. *)

Lemma ZOdiv_mult_cancel_r : forall a b c:Z,
 c<>0 -> (a*c)/(b*c) = a/b.
Proof. intros. zero_or_not b. apply Z.div_mul_cancel_r; auto. Qed.

Lemma ZOdiv_mult_cancel_l : forall a b c:Z,
 c<>0 -> (c*a)/(c*b) = a/b.
Proof.
 intros. rewrite (Zmult_comm c b). zero_or_not b.
 rewrite (Zmult_comm b c). apply Z.div_mul_cancel_l; auto.
Qed.

Lemma ZOmult_mod_distr_l: forall a b c,
  (c*a) mod (c*b) = c * (a mod b).
Proof.
 intros. zero_or_not c. rewrite (Zmult_comm c b). zero_or_not b.
 rewrite (Zmult_comm b c). apply Z.mul_mod_distr_l; auto.
Qed.

Lemma ZOmult_mod_distr_r: forall a b c,
  (a*c) mod (b*c) = (a mod b) * c.
Proof.
 intros. zero_or_not b. rewrite (Zmult_comm b c). zero_or_not c.
 rewrite (Zmult_comm c b). apply Z.mul_mod_distr_r; auto.
Qed.

(** Operations modulo. *)

Theorem ZOmod_mod: forall a n, (a mod n) mod n = a mod n.
Proof. intros. zero_or_not n. apply Z.mod_mod; auto. Qed.

Theorem ZOmult_mod: forall a b n,
 (a * b) mod n = ((a mod n) * (b mod n)) mod n.
Proof. intros. zero_or_not n. apply Z.mul_mod; auto. Qed.

(** addition and modulo

  Generally speaking, unlike with Zdiv, we don't have
       (a+b) mod n = (a mod n + b mod n) mod n
  for any a and b.
  For instance, take (8 + (-10)) mod 3 = -2 whereas
  (8 mod 3 + (-10 mod 3)) mod 3 = 1. *)

Theorem ZOplus_mod: forall a b n,
 0 <= a * b ->
 (a + b) mod n = (a mod n + b mod n) mod n.
Proof. intros. zero_or_not n. apply Z.add_mod; auto. Qed.

Lemma ZOplus_mod_idemp_l: forall a b n,
 0 <= a * b ->
 (a mod n + b) mod n = (a + b) mod n.
Proof. intros. zero_or_not n. apply Z.add_mod_idemp_l; auto. Qed.

Lemma ZOplus_mod_idemp_r: forall a b n,
 0 <= a*b ->
 (b + a mod n) mod n = (b + a) mod n.
Proof.
 intros. zero_or_not n. apply Z.add_mod_idemp_r; auto.
 rewrite Zmult_comm; auto. Qed.

Lemma ZOmult_mod_idemp_l: forall a b n, (a mod n * b) mod n = (a * b) mod n.
Proof. intros. zero_or_not n. apply Z.mul_mod_idemp_l; auto. Qed.

Lemma ZOmult_mod_idemp_r: forall a b n, (b * (a mod n)) mod n = (b * a) mod n.
Proof. intros. zero_or_not n. apply Z.mul_mod_idemp_r; auto. Qed.

(** Unlike with Zdiv, the following result is true without restrictions. *)

Lemma ZOdiv_ZOdiv : forall a b c, (a/b)/c = a/(b*c).
Proof.
 intros. zero_or_not b. rewrite Zmult_comm. zero_or_not c.
 rewrite Zmult_comm. apply Z.div_div; auto.
Qed.

(** A last inequality: *)

Theorem ZOdiv_mult_le:
 forall a b c, 0<=a -> 0<=b -> 0<=c -> c*(a/b) <= (c*a)/b.
Proof. intros. zero_or_not b. apply Z.div_mul_le; auto with zarith. Qed.

(** ZOmod is related to divisibility (see more in Znumtheory) *)

Lemma ZOmod_divides : forall a b,
 a mod b = 0 <-> exists c, a = b*c.
Proof. intros. zero_or_not b. firstorder. apply Z.mod_divides; auto. Qed.

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
