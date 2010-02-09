(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Contribution by Claude Marché and Xavier Urbain *)

(** Euclidean Division

    Defines first of function that allows Coq to normalize.
    Then only after proves the main required property.
*)

Require Export ZArith_base.
Require Import Zbool Omega ZArithRing Zcomplements Setoid Morphisms.
Require ZDivFloor.
Open Local Scope Z_scope.

(** * Definitions of Euclidian operations *)

(** Euclidean division of a positive by a integer
    (that is supposed to be positive).

    Total function than returns an arbitrary value when
    divisor is not positive

*)

Unboxed Fixpoint Zdiv_eucl_POS (a:positive) (b:Z) : Z * Z :=
  match a with
    | xH => if Zge_bool b 2 then (0, 1) else (1, 0)
    | xO a' =>
      let (q, r) := Zdiv_eucl_POS a' b in
	let r' := 2 * r in
	  if Zgt_bool b r' then (2 * q, r') else (2 * q + 1, r' - b)
    | xI a' =>
      let (q, r) := Zdiv_eucl_POS a' b in
	let r' := 2 * r + 1 in
	  if Zgt_bool b r' then (2 * q, r') else (2 * q + 1, r' - b)
  end.


(** Euclidean division of integers.

    Total function than returns (0,0) when dividing by 0.
*)

(**

  The pseudo-code is:

  if b = 0 : (0,0)

  if b <> 0 and a = 0 : (0,0)

  if b > 0 and a < 0 : let (q,r) = div_eucl_pos (-a) b in
                       if r = 0 then (-q,0) else (-(q+1),b-r)

  if b < 0 and a < 0 : let (q,r) = div_eucl (-a) (-b) in (q,-r)

  if b < 0 and a > 0 : let (q,r) = div_eucl a (-b) in
                       if r = 0 then (-q,0) else (-(q+1),b+r)

  In other word, when b is non-zero, q is chosen to be the greatest integer
  smaller or equal to a/b. And sgn(r)=sgn(b) and |r| < |b| (at least when
  r is not null).
*)

(* Nota: At least two others conventions also exist for euclidean division.
   They all satify the equation a=b*q+r, but differ on the choice of (q,r)
   on negative numbers.

   * Ocaml uses Round-Toward-Zero division: (-a)/b = a/(-b) = -(a/b).
     Hence (-a) mod b = - (a mod b)
           a mod (-b) = a mod b
     And: |r| < |b| and sgn(r) = sgn(a)  (notice the a here instead of b).

   * Another solution is to always pick a non-negative remainder:
     a=b*q+r with 0 <= r < |b|
*)

Definition Zdiv_eucl (a b:Z) : Z * Z :=
  match a, b with
    | Z0, _ => (0, 0)
    | _, Z0 => (0, 0)
    | Zpos a', Zpos _ => Zdiv_eucl_POS a' b
    | Zneg a', Zpos _ =>
      let (q, r) := Zdiv_eucl_POS a' b in
	match r with
	  | Z0 => (- q, 0)
	  | _ => (- (q + 1), b - r)
	end
    | Zneg a', Zneg b' => let (q, r) := Zdiv_eucl_POS a' (Zpos b') in (q, - r)
    | Zpos a', Zneg b' =>
      let (q, r) := Zdiv_eucl_POS a' (Zpos b') in
	match r with
	  | Z0 => (- q, 0)
	  | _ => (- (q + 1), b + r)
	end
  end.


(** Division and modulo are projections of [Zdiv_eucl] *)

Definition Zdiv (a b:Z) : Z := let (q, _) := Zdiv_eucl a b in q.

Definition Zmod (a b:Z) : Z := let (_, r) := Zdiv_eucl a b in r.

(** Syntax *)

Infix "/" := Zdiv : Z_scope.
Infix "mod" := Zmod (at level 40, no associativity) : Z_scope.

(* Tests:

Eval compute in (Zdiv_eucl 7 3).

Eval compute in (Zdiv_eucl (-7) 3).

Eval compute in (Zdiv_eucl 7 (-3)).

Eval compute in (Zdiv_eucl (-7) (-3)).

*)


(** * Main division theorem *)

(** First a lemma for two positive arguments *)

Lemma Z_div_mod_POS :
  forall b:Z,
    b > 0 ->
    forall a:positive,
      let (q, r) := Zdiv_eucl_POS a b in Zpos a = b * q + r /\ 0 <= r < b.
Proof.
simple induction a; cbv beta iota delta [Zdiv_eucl_POS] in |- *;
  fold Zdiv_eucl_POS in |- *; cbv zeta.

intro p; case (Zdiv_eucl_POS p b); intros q r [H0 H1].
generalize (Zgt_cases b (2 * r + 1)).
case (Zgt_bool b (2 * r + 1));
 (rewrite BinInt.Zpos_xI; rewrite H0; split; [ ring | omega ]).

intros p; case (Zdiv_eucl_POS p b); intros q r [H0 H1].
generalize (Zgt_cases b (2 * r)).
case (Zgt_bool b (2 * r)); rewrite BinInt.Zpos_xO;
 change (Zpos (xO p)) with (2 * Zpos p) in |- *; rewrite H0;
 (split; [ ring | omega ]).

generalize (Zge_cases b 2).
case (Zge_bool b 2); (intros; split; [ try ring | omega ]).
omega.
Qed.

(** Then the usual situation of a positive [b] and no restriction on [a] *)

Theorem Z_div_mod :
  forall a b:Z,
    b > 0 -> let (q, r) := Zdiv_eucl a b in a = b * q + r /\ 0 <= r < b.
Proof.
  intros a b; case a; case b; try (simpl in |- *; intros; omega).
  unfold Zdiv_eucl in |- *; intros; apply Z_div_mod_POS; trivial.

  intros; discriminate.

  intros.
  generalize (Z_div_mod_POS (Zpos p) H p0).
  unfold Zdiv_eucl in |- *.
  case (Zdiv_eucl_POS p0 (Zpos p)).
  intros z z0.
  case z0.

  intros [H1 H2].
  split; trivial.
  change (Zneg p0) with (- Zpos p0); rewrite H1; ring.

  intros p1 [H1 H2].
  split; trivial.
  change (Zneg p0) with (- Zpos p0); rewrite H1; ring.
  generalize (Zorder.Zgt_pos_0 p1); omega.

  intros p1 [H1 H2].
  split; trivial.
  change (Zneg p0) with (- Zpos p0); rewrite H1; ring.
  generalize (Zorder.Zlt_neg_0 p1); omega.

  intros; discriminate.
Qed.

(** For stating the fully general result, let's give a short name
    to the condition on the remainder. *)

Definition Remainder r b :=  0 <= r < b \/ b < r <= 0.

(** Another equivalent formulation: *)

Definition Remainder_alt r b :=  Zabs r < Zabs b /\ Zsgn r <> - Zsgn b.

(* In the last formulation, [ Zsgn r <> - Zsgn b ] is less nice than saying
    [ Zsgn r = Zsgn b ], but at least it works even when [r] is null. *)

Lemma Remainder_equiv : forall r b, Remainder r b <-> Remainder_alt r b.
Proof.
 intros; unfold Remainder, Remainder_alt; omega with *.
Qed.

Hint Unfold Remainder.

(** Now comes the fully general result about Euclidean division. *)

Theorem Z_div_mod_full :
  forall a b:Z,
    b <> 0 -> let (q, r) := Zdiv_eucl a b in a = b * q + r /\ Remainder r b.
Proof.
  destruct b as [|b|b].
  (* b = 0 *)
  intro H; elim H; auto.
  (* b > 0 *)
  intros _.
  assert (Zpos b > 0) by auto with zarith.
  generalize (Z_div_mod a (Zpos b) H).
  destruct Zdiv_eucl as (q,r); intuition; simpl; auto.
  (* b < 0 *)
  intros _.
  assert (Zpos b > 0) by auto with zarith.
  generalize (Z_div_mod a (Zpos b) H).
  unfold Remainder.
  destruct a as [|a|a].
  (* a = 0 *)
  simpl; intuition.
  (* a > 0 *)
  unfold Zdiv_eucl; destruct Zdiv_eucl_POS as (q,r).
  destruct r as [|r|r]; [ | | omega with *].
  rewrite <- Zmult_opp_comm; simpl Zopp; intuition.
  rewrite <- Zmult_opp_comm; simpl Zopp.
  rewrite Zmult_plus_distr_r; omega with *.
  (* a < 0 *)
  unfold Zdiv_eucl.
  generalize (Z_div_mod_POS (Zpos b) H a).
  destruct Zdiv_eucl_POS as (q,r).
  destruct r as [|r|r]; change (Zneg b) with (-Zpos b).
  rewrite Zmult_opp_comm; omega with *.
  rewrite <- Zmult_opp_comm, Zmult_plus_distr_r;
   repeat rewrite Zmult_opp_comm; omega.
  rewrite Zmult_opp_comm; omega with *.
Qed.

(** The same results as before, stated separately in terms of Zdiv and Zmod *)

Lemma Z_mod_remainder : forall a b:Z, b<>0 -> Remainder (a mod b) b.
Proof.
  unfold Zmod; intros a b Hb; generalize (Z_div_mod_full a b Hb); auto.
  destruct Zdiv_eucl; tauto.
Qed.

Lemma Z_mod_lt : forall a b:Z, b > 0 -> 0 <= a mod b < b.
Proof.
  unfold Zmod; intros a b Hb; generalize (Z_div_mod a b Hb).
  destruct Zdiv_eucl; tauto.
Qed.

Lemma Z_mod_neg : forall a b:Z, b < 0 -> b < a mod b <= 0.
Proof.
  unfold Zmod; intros a b Hb.
  assert (Hb' : b<>0) by (auto with zarith).
  generalize (Z_div_mod_full a b Hb').
  destruct Zdiv_eucl.
  unfold Remainder; intuition.
Qed.

Lemma Z_div_mod_eq_full : forall a b:Z, b <> 0 -> a = b*(a/b) + (a mod b).
Proof.
  unfold Zdiv, Zmod; intros a b Hb; generalize (Z_div_mod_full a b Hb).
  destruct Zdiv_eucl; tauto.
Qed.

Lemma Z_div_mod_eq : forall a b:Z, b > 0 -> a = b*(a/b) + (a mod b).
Proof.
  intros; apply Z_div_mod_eq_full; auto with zarith.
Qed.

Lemma Zmod_eq_full : forall a b:Z, b<>0 -> a mod b = a - (a/b)*b.
Proof.
  intros.
  rewrite <- Zeq_plus_swap, Zplus_comm, Zmult_comm; symmetry.
  apply Z_div_mod_eq_full; auto.
Qed.

Lemma Zmod_eq : forall a b:Z, b>0 -> a mod b = a - (a/b)*b.
Proof.
  intros.
  rewrite <- Zeq_plus_swap, Zplus_comm, Zmult_comm; symmetry.
  apply Z_div_mod_eq; auto.
Qed.

(** We know enough to prove that [Zdiv] and [Zmod] are instances of
    one of the abstract Euclidean divisions of Numbers.
    We hence benefit from generic results about this abstract division. *)

Module Z.

 Definition div := Zdiv.
 Definition modulo := Zmod.
 Local Obligation Tactic := simpl_relation.
 Program Instance div_wd : Proper (eq==>eq==>eq) div.
 Program Instance mod_wd : Proper (eq==>eq==>eq) modulo.

 Definition div_mod := Z_div_mod_eq_full.
 Definition mod_pos_bound : forall a b:Z, 0<b -> 0<=a mod b<b.
 Proof. intros; apply Z_mod_lt; auto with zarith. Qed.
 Definition mod_neg_bound := Z_mod_neg.

 Include ZBinary.Z <+ ZDivFloor.ZDivPropFunct.

End Z.

(** Existence theorem *)

Theorem Zdiv_eucl_exist : forall (b:Z)(Hb:b>0)(a:Z),
 {qr : Z * Z | let (q, r) := qr in a = b * q + r /\ 0 <= r < b}.
Proof.
  intros b Hb a.
  exists (Zdiv_eucl a b).
  exact (Z_div_mod a b Hb).
Qed.

Implicit Arguments Zdiv_eucl_exist.


(** Uniqueness theorems *)

Theorem Zdiv_mod_unique :
 forall b q1 q2 r1 r2:Z,
  0 <= r1 < Zabs b -> 0 <= r2 < Zabs b ->
  b*q1+r1 = b*q2+r2 -> q1=q2 /\ r1=r2.
Proof.
intros b q1 q2 r1 r2 Hr1 Hr2 H.
destruct (Z_eq_dec q1 q2) as [Hq|Hq].
split; trivial.
rewrite Hq in H; omega.
elim (Zlt_not_le (Zabs (r2 - r1)) (Zabs b)).
omega with *.
replace (r2-r1) with (b*(q1-q2)) by (rewrite Zmult_minus_distr_l; omega).
replace (Zabs b) with ((Zabs b)*1) by ring.
rewrite Zabs_Zmult.
apply Zmult_le_compat_l; auto with *.
omega with *.
Qed.

Theorem Zdiv_mod_unique_2 :
 forall b q1 q2 r1 r2:Z,
  Remainder r1 b -> Remainder r2 b ->
  b*q1+r1 = b*q2+r2 -> q1=q2 /\ r1=r2.
Proof. exact Z.div_mod_unique. Qed.

Theorem Zdiv_unique_full:
 forall a b q r, Remainder r b ->
   a = b*q + r -> q = a/b.
Proof. exact Z.div_unique. Qed.

Theorem Zdiv_unique:
 forall a b q r, 0 <= r < b ->
   a = b*q + r -> q = a/b.
Proof. intros; eapply Zdiv_unique_full; eauto. Qed.

Theorem Zmod_unique_full:
 forall a b q r, Remainder r b ->
  a = b*q + r ->  r = a mod b.
Proof. exact Z.mod_unique. Qed.

Theorem Zmod_unique:
 forall a b q r, 0 <= r < b ->
  a = b*q + r -> r = a mod b.
Proof. intros; eapply Zmod_unique_full; eauto. Qed.

(** * Basic values of divisions and modulo. *)

Lemma Zmod_0_l: forall a, 0 mod a = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma Zmod_0_r: forall a, a mod 0 = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma Zdiv_0_l: forall a, 0/a = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma Zdiv_0_r: forall a, a/0 = 0.
Proof.
  destruct a; simpl; auto.
Qed.

Ltac zero_or_not a :=
  destruct (Z_eq_dec a 0);
  [subst; rewrite ?Zmod_0_l, ?Zdiv_0_l, ?Zmod_0_r, ?Zdiv_0_r;
   auto with zarith|].

Lemma Zmod_1_r: forall a, a mod 1 = 0.
Proof. intros. zero_or_not a. apply Z.mod_1_r. Qed.

Lemma Zdiv_1_r: forall a, a/1 = a.
Proof. intros. zero_or_not a. apply Z.div_1_r. Qed.

Hint Resolve Zmod_0_l Zmod_0_r Zdiv_0_l Zdiv_0_r Zdiv_1_r Zmod_1_r
 : zarith.

Lemma Zdiv_1_l: forall a, 1 < a -> 1/a = 0.
Proof. exact Z.div_1_l. Qed.

Lemma Zmod_1_l: forall a, 1 < a ->  1 mod a = 1.
Proof. exact Z.mod_1_l. Qed.

Lemma Z_div_same_full : forall a:Z, a<>0 -> a/a = 1.
Proof. exact Z.div_same. Qed.

Lemma Z_mod_same_full : forall a, a mod a = 0.
Proof. intros. zero_or_not a. apply Z.mod_same; auto. Qed.

Lemma Z_mod_mult : forall a b, (a*b) mod b = 0.
Proof. intros. zero_or_not b. apply Z.mod_mul. auto. Qed.

Lemma Z_div_mult_full : forall a b:Z, b <> 0 -> (a*b)/b = a.
Proof. exact Z.div_mul. Qed.

(** * Order results about Zmod and Zdiv *)

(* Division of positive numbers is positive. *)

Lemma Z_div_pos: forall a b, b > 0 -> 0 <= a -> 0 <= a/b.
Proof. intros. apply Z.div_pos; auto with zarith. Qed.

Lemma Z_div_ge0: forall a b, b > 0 -> a >= 0 -> a/b >=0.
Proof.
  intros; generalize (Z_div_pos a b H); auto with zarith.
Qed.

(** As soon as the divisor is greater or equal than 2,
    the division is strictly decreasing. *)

Lemma Z_div_lt : forall a b:Z, b >= 2 -> a > 0 -> a/b < a.
Proof. intros. apply Z.div_lt; auto with zarith. Qed.

(** A division of a small number by a bigger one yields zero. *)

Theorem Zdiv_small: forall a b, 0 <= a < b -> a/b = 0.
Proof. exact Z.div_small. Qed.

(** Same situation, in term of modulo: *)

Theorem Zmod_small: forall a n, 0 <= a < n -> a mod n = a.
Proof. exact Z.mod_small. Qed.

(** [Zge] is compatible with a positive division. *)

Lemma Z_div_ge : forall a b c:Z, c > 0 -> a >= b -> a/c >= b/c.
Proof. intros. apply Zle_ge. apply Z.div_le_mono; auto with zarith. Qed.

(** Same, with [Zle]. *)

Lemma Z_div_le : forall a b c:Z, c > 0 -> a <= b -> a/c <= b/c.
Proof. intros. apply Z.div_le_mono; auto with zarith. Qed.

(** With our choice of division, rounding of (a/b) is always done toward bottom: *)

Lemma Z_mult_div_ge : forall a b:Z, b > 0 -> b*(a/b) <= a.
Proof. intros. apply Z.mul_div_le; auto with zarith. Qed.

Lemma Z_mult_div_ge_neg : forall a b:Z, b < 0 -> b*(a/b) >= a.
Proof. intros. apply Zle_ge. apply Z.mul_div_ge; auto with zarith. Qed.

(** The previous inequalities are exact iff the modulo is zero. *)

Lemma Z_div_exact_full_1 : forall a b:Z, a = b*(a/b) -> a mod b = 0.
Proof. intros a b. zero_or_not b. rewrite Z.div_exact; auto. Qed.

Lemma Z_div_exact_full_2 : forall a b:Z, b <> 0 -> a mod b = 0 -> a = b*(a/b).
Proof. intros; rewrite Z.div_exact; auto. Qed.

(** A modulo cannot grow beyond its starting point. *)

Theorem Zmod_le: forall a b, 0 < b -> 0 <= a -> a mod b <= a.
Proof. intros. apply Z.mod_le; auto. Qed.

(** Some additionnal inequalities about Zdiv. *)

Theorem Zdiv_lt_upper_bound:
  forall a b q, 0 < b -> a < q*b -> a/b < q.
Proof. intros a b q; rewrite Zmult_comm; apply Z.div_lt_upper_bound. Qed.

Theorem Zdiv_le_upper_bound:
  forall a b q, 0 < b -> a <= q*b -> a/b <= q.
Proof. intros a b q; rewrite Zmult_comm; apply Z.div_le_upper_bound. Qed.

Theorem Zdiv_le_lower_bound:
  forall a b q, 0 < b -> q*b <= a -> q <= a/b.
Proof. intros a b q; rewrite Zmult_comm; apply Z.div_le_lower_bound. Qed.

(** A division of respect opposite monotonicity for the divisor *)

Lemma Zdiv_le_compat_l: forall p q r, 0 <= p -> 0 < q < r ->
    p / r <= p / q.
Proof. intros; apply Z.div_le_compat_l; auto with zarith. Qed.

Theorem Zdiv_sgn: forall a b,
  0 <= Zsgn (a/b) * Zsgn a * Zsgn b.
Proof.
  destruct a as [ |a|a]; destruct b as [ |b|b]; simpl; auto with zarith;
  generalize (Z_div_pos (Zpos a) (Zpos b)); unfold Zdiv, Zdiv_eucl;
  destruct Zdiv_eucl_POS as (q,r); destruct r; omega with *.
Qed.

(** * Relations between usual operations and Zmod and Zdiv *)

Lemma Z_mod_plus_full : forall a b c:Z, (a + b * c) mod c = a mod c.
Proof. intros. zero_or_not c. apply Z.mod_add; auto. Qed.

Lemma Z_div_plus_full : forall a b c:Z, c <> 0 -> (a + b * c) / c = a / c + b.
Proof. exact Z.div_add. Qed.

Theorem Z_div_plus_full_l: forall a b c : Z, b <> 0 -> (a * b + c) / b = a + c / b.
Proof. exact Z.div_add_l. Qed.

(** [Zopp] and [Zdiv], [Zmod].
    Due to the choice of convention for our Euclidean division,
    some of the relations about [Zopp] and divisions are rather complex. *)

Lemma Zdiv_opp_opp : forall a b:Z, (-a)/(-b) = a/b.
Proof. intros. zero_or_not b. apply Z.div_opp_opp; auto. Qed.

Lemma Zmod_opp_opp : forall a b:Z, (-a) mod (-b) = - (a mod b).
Proof. intros. zero_or_not b. apply Z.mod_opp_opp; auto. Qed.

Lemma Z_mod_zero_opp_full : forall a b:Z, a mod b = 0 -> (-a) mod b = 0.
Proof. intros. zero_or_not b. apply Z.mod_opp_l_z; auto. Qed.

Lemma Z_mod_nz_opp_full : forall a b:Z, a mod b <> 0 ->
 (-a) mod b = b - (a mod b).
Proof. intros. zero_or_not b. apply Z.mod_opp_l_nz; auto. Qed.

Lemma Z_mod_zero_opp_r : forall a b:Z, a mod b = 0 -> a mod (-b) = 0.
Proof. intros. zero_or_not b. apply Z.mod_opp_r_z; auto. Qed.

Lemma Z_mod_nz_opp_r : forall a b:Z, a mod b <> 0 ->
 a mod (-b) = (a mod b) - b.
Proof. intros. zero_or_not b. apply Z.mod_opp_r_nz; auto. Qed.

Lemma Z_div_zero_opp_full : forall a b:Z, a mod b = 0 -> (-a)/b = -(a/b).
Proof. intros. zero_or_not b. apply Z.div_opp_l_z; auto. Qed.

Lemma Z_div_nz_opp_full : forall a b:Z, a mod b <> 0 ->
 (-a)/b = -(a/b)-1.
Proof. intros a b. zero_or_not b. intros; rewrite Z.div_opp_l_nz; auto. Qed.

Lemma Z_div_zero_opp_r : forall a b:Z, a mod b = 0 -> a/(-b) = -(a/b).
Proof. intros. zero_or_not b. apply Z.div_opp_r_z; auto. Qed.

Lemma Z_div_nz_opp_r : forall a b:Z, a mod b <> 0 ->
 a/(-b) = -(a/b)-1.
Proof. intros a b. zero_or_not b. intros; rewrite Z.div_opp_r_nz; auto. Qed.

(** Cancellations. *)

Lemma Zdiv_mult_cancel_r : forall a b c:Z,
 c <> 0 -> (a*c)/(b*c) = a/b.
Proof. intros. zero_or_not b. apply Z.div_mul_cancel_r; auto. Qed.

Lemma Zdiv_mult_cancel_l : forall a b c:Z,
 c<>0 -> (c*a)/(c*b) = a/b.
Proof.
 intros. rewrite (Zmult_comm c b); zero_or_not b.
 rewrite (Zmult_comm b c). apply Z.div_mul_cancel_l; auto.
Qed.

Lemma Zmult_mod_distr_l: forall a b c,
  (c*a) mod (c*b) = c * (a mod b).
Proof.
 intros. zero_or_not c. rewrite (Zmult_comm c b); zero_or_not b.
 rewrite (Zmult_comm b c). apply Z.mul_mod_distr_l; auto.
Qed.

Lemma Zmult_mod_distr_r: forall a b c,
  (a*c) mod (b*c) = (a mod b) * c.
Proof.
 intros. zero_or_not b. rewrite (Zmult_comm b c); zero_or_not c.
 rewrite (Zmult_comm c b). apply Z.mul_mod_distr_r; auto.
Qed.

(** Operations modulo. *)

Theorem Zmod_mod: forall a n, (a mod n) mod n = a mod n.
Proof. intros. zero_or_not n. apply Z.mod_mod; auto. Qed.

Theorem Zmult_mod: forall a b n,
 (a * b) mod n = ((a mod n) * (b mod n)) mod n.
Proof. intros. zero_or_not n. apply Z.mul_mod; auto. Qed.

Theorem Zplus_mod: forall a b n,
 (a + b) mod n = (a mod n + b mod n) mod n.
Proof. intros. zero_or_not n. apply Z.add_mod; auto. Qed.

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

(** For a specific number N, equality modulo N is hence a nice setoid
   equivalence, compatible with [+], [-] and [*]. *)

Definition eqm N a b := (a mod N = b mod N).

Lemma eqm_refl N : forall a, (eqm N) a a.
Proof. unfold eqm; auto. Qed.

Lemma eqm_sym N : forall a b, (eqm N) a b -> (eqm N) b a.
Proof. unfold eqm; auto. Qed.

Lemma eqm_trans N : forall a b c,
  (eqm N) a b -> (eqm N) b c -> (eqm N) a c.
Proof. unfold eqm; eauto with *. Qed.

Add Parametric Relation N : Z (eqm N)
  reflexivity proved by (eqm_refl N)
  symmetry proved by (eqm_sym N)
  transitivity proved by (eqm_trans N) as eqm_setoid.

Add Parametric Morphism N : Zplus
  with signature (eqm N) ==> (eqm N) ==> (eqm N) as Zplus_eqm.
Proof.
  unfold eqm; intros; rewrite Zplus_mod, H, H0, <- Zplus_mod; auto.
Qed.

Add Parametric Morphism N : Zminus
  with signature (eqm N) ==> (eqm N) ==> (eqm N) as Zminus_eqm.
Proof.
  unfold eqm; intros; rewrite Zminus_mod, H, H0, <- Zminus_mod; auto.
Qed.

Add Parametric Morphism N : Zmult
  with signature (eqm N) ==> (eqm N) ==> (eqm N) as Zmult_eqm.
Proof.
  unfold eqm; intros; rewrite Zmult_mod, H, H0, <- Zmult_mod; auto.
Qed.

Add Parametric Morphism N : Zopp
  with signature (eqm N) ==> (eqm N) as Zopp_eqm.
Proof.
  intros; change ((eqm N) (-x) (-y)) with ((eqm N) (0-x) (0-y)).
  rewrite H; red; auto.
Qed.

Lemma Zmod_eqm N : forall a, (eqm N) (a mod N) a.
Proof.
  intros; exact (Zmod_mod a N).
Qed.

(* NB: Zmod and Zdiv are not morphisms with respect to eqm.
    For instance, let (==) be (eqm 2). Then we have (3 == 1) but:
    ~ (3 mod 3 == 1 mod 3)
    ~ (1 mod 3 == 1 mod 1)
    ~ (3/3 == 1/3)
    ~ (1/3 == 1/1)
*)

Lemma Zdiv_Zdiv : forall a b c, 0<=b -> 0<=c -> (a/b)/c = a/(b*c).
Proof.
 intros. zero_or_not b. rewrite Zmult_comm. zero_or_not c.
 rewrite Zmult_comm. apply Z.div_div; auto with zarith.
Qed.

(** Unfortunately, the previous result isn't always true on negative numbers.
    For instance: 3/(-2)/(-2) = 1 <> 0 = 3 / (-2*-2) *)

(** A last inequality: *)

Theorem Zdiv_mult_le:
 forall a b c, 0<=a -> 0<=b -> 0<=c -> c*(a/b) <= (c*a)/b.
Proof.
 intros. zero_or_not b. apply Z.div_mul_le; auto with zarith. Qed.

(** Zmod is related to divisibility (see more in Znumtheory) *)

Lemma Zmod_divides : forall a b, b<>0 ->
 (a mod b = 0 <-> exists c, a = b*c).
Proof. exact Z.mod_divides. Qed.

(** * Compatibility *)

(** Weaker results kept only for compatibility *)

Lemma Z_mod_same : forall a, a > 0 -> a mod a = 0.
Proof.
  intros; apply Z_mod_same_full.
Qed.

Lemma Z_div_same : forall a, a > 0 -> a/a = 1.
Proof.
  intros; apply Z_div_same_full; auto with zarith.
Qed.

Lemma Z_div_plus : forall a b c:Z, c > 0 -> (a + b * c) / c = a / c + b.
Proof.
  intros; apply Z_div_plus_full; auto with zarith.
Qed.

Lemma Z_div_mult : forall a b:Z, b > 0 -> (a*b)/b = a.
Proof.
  intros; apply Z_div_mult_full; auto with zarith.
Qed.

Lemma Z_mod_plus : forall a b c:Z, c > 0 -> (a + b * c) mod c = a mod c.
Proof.
  intros; apply Z_mod_plus_full; auto with zarith.
Qed.

Lemma Z_div_exact_1 : forall a b:Z, b > 0 -> a = b*(a/b) -> a mod b = 0.
Proof.
  intros; apply Z_div_exact_full_1; auto with zarith.
Qed.

Lemma Z_div_exact_2 : forall a b:Z, b > 0 -> a mod b = 0 -> a = b*(a/b).
Proof.
  intros; apply Z_div_exact_full_2; auto with zarith.
Qed.

Lemma Z_mod_zero_opp : forall a b:Z, b > 0 -> a mod b = 0 -> (-a) mod b = 0.
Proof.
  intros; apply Z_mod_zero_opp_full; auto with zarith.
Qed.

(** * A direct way to compute Zmod *)

Fixpoint Zmod_POS (a : positive) (b : Z) : Z  :=
  match a with
   | xI a' =>
      let r := Zmod_POS a' b in
      let r' := (2 * r + 1) in
      if Zgt_bool b r' then r' else (r' - b)
   | xO a' =>
      let r := Zmod_POS a' b in
      let r' := (2 * r) in
      if Zgt_bool b r' then r' else (r' - b)
   | xH => if Zge_bool b 2 then 1 else 0
  end.

Definition Zmod' a b :=
  match a with
   | Z0 => 0
   | Zpos a' =>
      match b with
       | Z0 => 0
       | Zpos _ => Zmod_POS a' b
       | Zneg b' =>
          let r := Zmod_POS a' (Zpos b') in
          match r  with Z0 =>  0 |  _  =>   b + r end
      end
   | Zneg a' =>
      match b with
       | Z0 => 0
       | Zpos _ =>
          let r := Zmod_POS a' b in
          match r with Z0 =>  0 | _  =>  b - r end
       | Zneg b' => - (Zmod_POS a' (Zpos b'))
      end
  end.


Theorem Zmod_POS_correct: forall a b, Zmod_POS a b = (snd (Zdiv_eucl_POS a b)).
Proof.
  intros a b; elim a; simpl; auto.
  intros p Rec; rewrite  Rec.
  case (Zdiv_eucl_POS p b); intros z1 z2; simpl; auto.
  match goal with |- context [Zgt_bool _ ?X] => case (Zgt_bool b X) end; auto.
  intros p Rec; rewrite  Rec.
  case (Zdiv_eucl_POS p b); intros z1 z2; simpl; auto.
  match goal with |- context [Zgt_bool _ ?X] => case (Zgt_bool b X) end; auto.
  case (Zge_bool b 2); auto.
Qed.

Theorem Zmod'_correct: forall a b, Zmod' a b = Zmod a b.
Proof.
  intros a b; unfold Zmod; case a; simpl; auto.
  intros p; case b; simpl; auto.
  intros p1; refine (Zmod_POS_correct _ _); auto.
  intros p1; rewrite Zmod_POS_correct; auto.
  case (Zdiv_eucl_POS p (Zpos p1)); simpl; intros z1 z2; case z2; auto.
  intros p; case b; simpl; auto.
  intros p1; rewrite Zmod_POS_correct; auto.
  case (Zdiv_eucl_POS p (Zpos p1)); simpl; intros z1 z2; case z2; auto.
  intros p1; rewrite Zmod_POS_correct; simpl; auto.
  case (Zdiv_eucl_POS p (Zpos p1)); auto.
Qed.


(** Another convention is possible for division by negative numbers:
    * quotient is always the biggest integer smaller than or equal to a/b
    * remainder is hence always positive or null. *)

Theorem Zdiv_eucl_extended :
  forall b:Z,
    b <> 0 ->
    forall a:Z,
      {qr : Z * Z | let (q, r) := qr in a = b * q + r /\ 0 <= r < Zabs b}.
Proof.
  intros b Hb a.
  elim (Z_le_gt_dec 0 b); intro Hb'.
  cut (b > 0); [ intro Hb'' | omega ].
  rewrite Zabs_eq; [ apply Zdiv_eucl_exist; assumption | assumption ].
  cut (- b > 0); [ intro Hb'' | omega ].
  elim (Zdiv_eucl_exist Hb'' a); intros qr.
  elim qr; intros q r Hqr.
  exists (- q, r).
  elim Hqr; intros.
  split.
  rewrite <- Zmult_opp_comm; assumption.
  rewrite Zabs_non_eq; [ assumption | omega ].
Qed.

Implicit Arguments Zdiv_eucl_extended.

(** A third convention: Ocaml.

     See files ZOdiv_def.v and ZOdiv.v.

     Ocaml uses Round-Toward-Zero division: (-a)/b = a/(-b) = -(a/b).
     Hence (-a) mod b = - (a mod b)
           a mod (-b) = a mod b
     And: |r| < |b| and sgn(r) = sgn(a)  (notice the a here instead of b).
*)
