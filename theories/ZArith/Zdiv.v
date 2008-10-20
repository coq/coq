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
Require Import Zbool.
Require Import Omega.
Require Import ZArithRing.
Require Import Zcomplements.
Require Export Setoid.
Open Local Scope Z_scope.

(** * Definitions of Euclidian operations *)

(** Euclidean division of a positive by a integer 
    (that is supposed to be positive).

    Total function than returns an arbitrary value when
    divisor is not positive
  
*)

Unboxed Fixpoint Zdiv_eucl_POS (a:positive) (b:Z) {struct a} : 
  Z * Z :=
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
Proof.
unfold Remainder.
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

Theorem Zdiv_unique_full:
 forall a b q r, Remainder r b -> 
   a = b*q + r -> q = a/b.
Proof.
  intros.
  assert (b <> 0) by (unfold Remainder in *; omega with *).
  generalize (Z_div_mod_full a b H1).
  unfold Zdiv; destruct Zdiv_eucl as (q',r').
  intros (H2,H3); rewrite H2 in H0.
  destruct (Zdiv_mod_unique_2 b q q' r r'); auto.
Qed.

Theorem Zdiv_unique:
 forall a b q r, 0 <= r < b -> 
   a = b*q + r -> q = a/b.
Proof.
  intros; eapply Zdiv_unique_full; eauto.
Qed.

Theorem Zmod_unique_full:
 forall a b q r, Remainder r b ->
  a = b*q + r ->  r = a mod b.
Proof.
  intros.
  assert (b <> 0) by (unfold Remainder in *; omega with *).
  generalize (Z_div_mod_full a b H1).
  unfold Zmod; destruct Zdiv_eucl as (q',r').
  intros (H2,H3); rewrite H2 in H0.
  destruct (Zdiv_mod_unique_2 b q q' r r'); auto.
Qed.

Theorem Zmod_unique:
 forall a b q r, 0 <= r < b ->
  a = b*q + r -> r = a mod b.
Proof.
  intros; eapply Zmod_unique_full; eauto.
Qed.

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

Lemma Zmod_1_r: forall a, a mod 1 = 0.
Proof.
  intros; symmetry; apply Zmod_unique with a; auto with zarith.
Qed.

Lemma Zdiv_1_r: forall a, a/1 = a.
Proof.
  intros; symmetry; apply Zdiv_unique with 0; auto with zarith.
Qed.

Hint Resolve Zmod_0_l Zmod_0_r Zdiv_0_l Zdiv_0_r Zdiv_1_r Zmod_1_r 
 : zarith.

Lemma Zdiv_1_l: forall a, 1 < a -> 1/a = 0.
Proof.
  intros; symmetry; apply Zdiv_unique with 1; auto with zarith.
Qed.

Lemma Zmod_1_l: forall a, 1 < a ->  1 mod a = 1.
Proof.
  intros; symmetry; apply Zmod_unique with 0; auto with zarith.
Qed.

Lemma Z_div_same_full : forall a:Z, a<>0 -> a/a = 1.
Proof.
  intros; symmetry; apply Zdiv_unique_full with 0; auto with *; red; omega.
Qed.

Lemma Z_mod_same_full : forall a, a mod a = 0.
Proof.
  destruct a; intros; symmetry.
  compute; auto.
  apply Zmod_unique with 1; auto with *; omega with *.
  apply Zmod_unique_full with 1; auto with *; red; omega with *.
Qed.

Lemma Z_mod_mult : forall a b, (a*b) mod b = 0.
Proof.
  intros a b; destruct (Z_eq_dec b 0) as [Hb|Hb].
  subst; simpl; rewrite Zmod_0_r; auto.
  symmetry; apply Zmod_unique_full with a; [ red; omega | ring ].
Qed.

Lemma Z_div_mult_full : forall a b:Z, b <> 0 -> (a*b)/b = a.
Proof.
  intros; symmetry; apply Zdiv_unique_full with 0; auto with zarith; 
   [ red; omega | ring].
Qed.

(** * Order results about Zmod and Zdiv *)

(* Division of positive numbers is positive. *)

Lemma Z_div_pos: forall a b, b > 0 -> 0 <= a -> 0 <= a/b.
Proof.
  intros.
  rewrite (Z_div_mod_eq a b H) in H0.
  assert (H1:=Z_mod_lt a b H).
  destruct (Z_lt_le_dec (a/b) 0); auto.
  assert (b*(a/b) <= -b).
   replace (-b) with (b*-1); [ | ring].
   apply Zmult_le_compat_l; auto with zarith.
  omega.
Qed.

Lemma Z_div_ge0: forall a b, b > 0 -> a >= 0 -> a/b >=0.
Proof.
  intros; generalize (Z_div_pos a b H); auto with zarith.
Qed.

(** As soon as the divisor is greater or equal than 2, 
    the division is strictly decreasing. *)

Lemma Z_div_lt : forall a b:Z, b >= 2 -> a > 0 -> a/b < a.
Proof.
  intros. cut (b > 0); [ intro Hb | omega ].
  generalize (Z_div_mod a b Hb).
  cut (a >= 0); [ intro Ha | omega ].
  generalize (Z_div_ge0 a b Hb Ha).
  unfold Zdiv in |- *; case (Zdiv_eucl a b); intros q r H1 [H2 H3].
  cut (a >= 2 * q -> q < a); [ intro h; apply h; clear h | intros; omega ].
  apply Zge_trans with (b * q).
  omega.
  auto with zarith.
Qed.


(** A division of a small number by a bigger one yields zero. *)

Theorem Zdiv_small: forall a b, 0 <= a < b -> a/b = 0.
Proof.
  intros a b H; apply sym_equal; apply Zdiv_unique with a; auto with zarith.
Qed.

(** Same situation, in term of modulo: *)

Theorem Zmod_small: forall a n, 0 <= a < n -> a mod n = a.
Proof.
  intros a b H; apply sym_equal; apply Zmod_unique with 0; auto with zarith.
Qed.

(** [Zge] is compatible with a positive division. *)

Lemma Z_div_ge : forall a b c:Z, c > 0 -> a >= b -> a/c >= b/c.
Proof.
  intros a b c cPos aGeb.
  generalize (Z_div_mod_eq a c cPos).
  generalize (Z_mod_lt a c cPos).
  generalize (Z_div_mod_eq b c cPos).
  generalize (Z_mod_lt b c cPos).
  intros.
  elim (Z_ge_lt_dec (a / c) (b / c)); trivial.
  intro.
  absurd (b - a >= 1).
  omega.
  replace (b-a) with (c * (b/c-a/c) + b mod c - a mod c) by 
    (symmetry; pattern a at 1; rewrite H2; pattern b at 1; rewrite H0; ring).
  assert (c * (b / c - a / c) >= c * 1).
  apply Zmult_ge_compat_l.
  omega.
  omega.
  assert (c * 1 = c).
  ring.
  omega.
Qed.

(** Same, with [Zle]. *)

Lemma Z_div_le : forall a b c:Z, c > 0 -> a <= b -> a/c <= b/c.
Proof.
  intros a b c H H0.
  apply Zge_le.
  apply Z_div_ge; auto with *.
Qed.

(** With our choice of division, rounding of (a/b) is always done toward bottom: *)

Lemma Z_mult_div_ge : forall a b:Z, b > 0 -> b*(a/b) <= a.
Proof.
  intros a b H; generalize (Z_div_mod_eq a b H) (Z_mod_lt a b H); omega.
Qed.

Lemma Z_mult_div_ge_neg : forall a b:Z, b < 0 -> b*(a/b) >= a.
Proof.
  intros a b H.
  generalize (Z_div_mod_eq_full a _ (Zlt_not_eq _ _ H)) (Z_mod_neg a _ H); omega.
Qed.

(** The previous inequalities are exact iff the modulo is zero. *)

Lemma Z_div_exact_full_1 : forall a b:Z, a = b*(a/b) -> a mod b = 0.
Proof.
  intros; destruct (Z_eq_dec b 0) as [Hb|Hb].
  subst b; simpl in *; subst; auto.
  generalize (Z_div_mod_eq_full a b Hb); omega.
Qed.

Lemma Z_div_exact_full_2 : forall a b:Z, b <> 0 -> a mod b = 0 -> a = b*(a/b).
Proof.
  intros; generalize (Z_div_mod_eq_full a b H); omega.
Qed.

(** A modulo cannot grow beyond its starting point. *)

Theorem Zmod_le: forall a b, 0 < b -> 0 <= a -> a mod b <= a.
Proof. 
  intros a b H1 H2; case (Zle_or_lt b a); intros H3.
  case (Z_mod_lt a b); auto with zarith.
  rewrite Zmod_small; auto with zarith.
Qed.

(** Some additionnal inequalities about Zdiv. *)

Theorem Zdiv_le_upper_bound: 
  forall a b q, 0 <= a -> 0 < b -> a <= q*b -> a/b <= q.
Proof.
  intros a b q H1 H2 H3.
  apply Zmult_le_reg_r with b; auto with zarith.
  apply Zle_trans with (2 := H3).
  pattern a at 2; rewrite (Z_div_mod_eq a b); auto with zarith.
  rewrite (Zmult_comm b); case (Z_mod_lt a b); auto with zarith.
Qed.

Theorem Zdiv_lt_upper_bound: 
  forall a b q, 0 <= a -> 0 < b -> a < q*b -> a/b < q.
Proof.
  intros a b q H1 H2 H3.
  apply Zmult_lt_reg_r with b; auto with zarith.
  apply Zle_lt_trans with (2 := H3).
  pattern a at 2; rewrite (Z_div_mod_eq a b); auto with zarith.
  rewrite (Zmult_comm b); case (Z_mod_lt a b); auto with zarith.
Qed.

Theorem Zdiv_le_lower_bound: 
  forall a b q, 0 <= a -> 0 < b -> q*b <= a -> q <= a/b.
Proof.
  intros a b q H1 H2 H3.
  assert (q < a / b + 1); auto with zarith.
  apply Zmult_lt_reg_r with b; auto with zarith.
  apply Zle_lt_trans with (1 := H3).
  pattern a at 1; rewrite (Z_div_mod_eq a b); auto with zarith.
  rewrite Zmult_plus_distr_l; rewrite (Zmult_comm b); case (Z_mod_lt a b);
   auto with zarith.
Qed.


(** A division of respect opposite monotonicity for the divisor *)

Lemma Zdiv_le_compat_l: forall p q r, 0 <= p -> 0 < q < r ->
    p / r <= p / q.
Proof.
  intros p q r H H1. 
  apply Zdiv_le_lower_bound; auto with zarith.
  rewrite Zmult_comm.
  pattern p at 2; rewrite (Z_div_mod_eq p r); auto with zarith.
  apply Zle_trans with (r * (p / r)); auto with zarith.
  apply Zmult_le_compat_r; auto with zarith.
  apply Zdiv_le_lower_bound; auto with zarith.
  case (Z_mod_lt p r); auto with zarith.
Qed.

Theorem Zdiv_sgn: forall a b, 
  0 <= Zsgn (a/b) * Zsgn a * Zsgn b.
Proof.
  destruct a as [ |a|a]; destruct b as [ |b|b]; simpl; auto with zarith; 
  generalize (Z_div_pos (Zpos a) (Zpos b)); unfold Zdiv, Zdiv_eucl; 
  destruct Zdiv_eucl_POS as (q,r); destruct r; omega with *.
Qed.

(** * Relations between usual operations and Zmod and Zdiv *)

Lemma Z_mod_plus_full : forall a b c:Z, (a + b * c) mod c = a mod c.
Proof.
  intros; destruct (Z_eq_dec c 0) as [Hc|Hc].
  subst; do 2 rewrite Zmod_0_r; auto.
  symmetry; apply Zmod_unique_full with (a/c+b); auto with zarith.
  red; generalize (Z_mod_lt a c)(Z_mod_neg a c); omega.
  rewrite Zmult_plus_distr_r, Zmult_comm.
  generalize (Z_div_mod_eq_full a c Hc); omega.
Qed.

Lemma Z_div_plus_full : forall a b c:Z, c <> 0 -> (a + b * c) / c = a / c + b.
Proof.
  intro; symmetry.
  apply Zdiv_unique_full with (a mod c); auto with zarith.
  red; generalize (Z_mod_lt a c)(Z_mod_neg a c); omega.
  rewrite Zmult_plus_distr_r, Zmult_comm.
  generalize (Z_div_mod_eq_full a c H); omega.
Qed.

Theorem Z_div_plus_full_l: forall a b c : Z, b <> 0 -> (a * b + c) / b = a + c / b.
Proof.
  intros a b c H; rewrite Zplus_comm; rewrite Z_div_plus_full;
  try apply Zplus_comm; auto with zarith. 
Qed.

(** [Zopp] and [Zdiv], [Zmod].
    Due to the choice of convention for our Euclidean division, 
    some of the relations about [Zopp] and divisions are rather complex. *) 

Lemma Zdiv_opp_opp : forall a b:Z, (-a)/(-b) = a/b.
Proof.
  intros [|a|a] [|b|b]; try reflexivity; unfold Zdiv; simpl;
  destruct (Zdiv_eucl_POS a (Zpos b)); destruct z0; try reflexivity.
Qed.

Lemma Zmod_opp_opp : forall a b:Z, (-a) mod (-b) = - (a mod b).
Proof.
  intros; destruct (Z_eq_dec b 0) as [Hb|Hb].
  subst; do 2 rewrite Zmod_0_r; auto.
  intros; symmetry.
  apply Zmod_unique_full with ((-a)/(-b)); auto.
  generalize (Z_mod_remainder a b Hb); destruct 1; [right|left]; omega.
  rewrite Zdiv_opp_opp.
  pattern a at 1; rewrite (Z_div_mod_eq_full a b Hb); ring.
Qed.

Lemma Z_mod_zero_opp_full : forall a b:Z, a mod b = 0 -> (-a) mod b = 0.
Proof.
  intros; destruct (Z_eq_dec b 0) as [Hb|Hb].
  subst; rewrite Zmod_0_r; auto.
  rewrite Z_div_exact_full_2 with a b; auto.
  replace (- (b * (a / b))) with (0 + - (a / b) * b).
  rewrite Z_mod_plus_full; auto.
  ring.
Qed.

Lemma Z_mod_nz_opp_full : forall a b:Z, a mod b <> 0 -> 
 (-a) mod b = b - (a mod b).
Proof.
  intros.
  assert (b<>0) by (contradict H; subst; rewrite Zmod_0_r; auto).
  symmetry; apply Zmod_unique_full with (-1-a/b); auto.
  generalize (Z_mod_remainder a b H0); destruct 1; [left|right]; omega.
  rewrite Zmult_minus_distr_l.
  pattern a at 1; rewrite (Z_div_mod_eq_full a b H0); ring.
Qed.

Lemma Z_mod_zero_opp_r : forall a b:Z, a mod b = 0 -> a mod (-b) = 0.
Proof.
  intros.
  rewrite <- (Zopp_involutive a).
  rewrite Zmod_opp_opp.
  rewrite Z_mod_zero_opp_full; auto.
Qed.

Lemma Z_mod_nz_opp_r : forall a b:Z, a mod b <> 0 -> 
 a mod (-b) = (a mod b) - b.
Proof.
  intros.
  pattern a at 1; rewrite <- (Zopp_involutive a).
  rewrite Zmod_opp_opp.
  rewrite Z_mod_nz_opp_full; auto; omega.
Qed.

Lemma Z_div_zero_opp_full : forall a b:Z, a mod b = 0 -> (-a)/b = -(a/b).
Proof.
  intros; destruct (Z_eq_dec b 0) as [Hb|Hb].
  subst; do 2 rewrite Zdiv_0_r; auto.
  symmetry; apply Zdiv_unique_full with 0; auto.
  red; omega.
  pattern a at 1; rewrite (Z_div_mod_eq_full a b Hb).
  rewrite H; ring.
Qed.

Lemma Z_div_nz_opp_full : forall a b:Z, a mod b <> 0 -> 
 (-a)/b = -(a/b)-1.
Proof.
  intros.
  assert (b<>0) by (contradict H; subst; rewrite Zmod_0_r; auto).
  symmetry; apply Zdiv_unique_full with (b-a mod b); auto.
  generalize (Z_mod_remainder a b H0); destruct 1; [left|right]; omega.
  pattern a at 1; rewrite (Z_div_mod_eq_full a b H0); ring.
Qed.

Lemma Z_div_zero_opp_r : forall a b:Z, a mod b = 0 -> a/(-b) = -(a/b).
Proof.
  intros.
  pattern a at 1; rewrite <- (Zopp_involutive a).
  rewrite Zdiv_opp_opp.
  rewrite Z_div_zero_opp_full; auto.
Qed.

Lemma Z_div_nz_opp_r : forall a b:Z, a mod b <> 0 -> 
 a/(-b) = -(a/b)-1.
Proof.
  intros.
  pattern a at 1; rewrite <- (Zopp_involutive a).
  rewrite Zdiv_opp_opp.
  rewrite Z_div_nz_opp_full; auto; omega.
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
  intros a b c Hb Hc.
  destruct (Zle_lt_or_eq _ _ Hb); [ | subst; rewrite Zdiv_0_r, Zdiv_0_r, Zdiv_0_l; auto].
  destruct (Zle_lt_or_eq _ _ Hc); [ | subst; rewrite Zmult_0_r, Zdiv_0_r, Zdiv_0_r; auto].
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
 forall a b c, 0<=a -> 0<=b -> 0<=c -> c*(a/b) <= (c*a)/b.
Proof.
  intros a b c H1 H2 H3.
  destruct (Zle_lt_or_eq _ _ H2); 
   [ | subst; rewrite Zdiv_0_r, Zdiv_0_r, Zmult_0_r; auto].
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

(** Zmod is related to divisibility (see more in Znumtheory) *)

Lemma Zmod_divides : forall a b, b<>0 -> 
 (a mod b = 0 <-> exists c, a = b*c).
Proof.
 split; intros.
 exists (a/b).
 pattern a at 1; rewrite (Z_div_mod_eq_full a b); auto with zarith.
 destruct H0 as [c Hc].
 symmetry.
 apply Zmod_unique_full with c; auto with zarith.
 red; omega with *.
Qed.

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

Fixpoint Zmod_POS (a : positive) (b : Z) {struct a} : Z  :=
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
