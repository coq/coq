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
  smaller or equal to a/b. And sgn(r)=sgn(b) and |r| < |b|.

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

Eval Compute in `(Zdiv_eucl 7 3)`. 

Eval Compute in `(Zdiv_eucl (-7) 3)`.

Eval Compute in `(Zdiv_eucl 7 (-3))`.

Eval Compute in `(Zdiv_eucl (-7) (-3))`.

*)


(** * Main division theorem *) 

(** First a lemma for positive *)

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
  replace (Zneg p0) with (- Zpos p0); [ rewrite H1; ring | trivial ].
  
  intros p1 [H1 H2].
  split; trivial.
  replace (Zneg p0) with (- Zpos p0); [ rewrite H1; ring | trivial ].
  generalize (Zorder.Zgt_pos_0 p1); omega.
  
  intros p1 [H1 H2].
  split; trivial.
  replace (Zneg p0) with (- Zpos p0); [ rewrite H1; ring | trivial ].
  generalize (Zorder.Zlt_neg_0 p1); omega.
  
  intros; discriminate.
Qed.

(** Existence theorems *)

Theorem Zdiv_eucl_exist :
  forall b:Z,
    b > 0 ->
    forall a:Z, {qr : Z * Z | let (q, r) := qr in a = b * q + r /\ 0 <= r < b}.
Proof.
  intros b Hb a.
  exists (Zdiv_eucl a b).
  exact (Z_div_mod a b Hb).
Qed.

Implicit Arguments Zdiv_eucl_exist.

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

(** Uniqueness theorems *)

Theorem Zdiv_mod_unique :
 forall b q1 q2 r1 r2:Z,
  0 <= r1 < Zabs b -> 0 <= r2 < Zabs b ->
  b*q1 + r1=b*q2+r2 -> q1=q2/\r1=r2.
Proof.
intros b q1 q2 r1 r2 Hr1 Hr2 H.
assert (H0:=Zeq_minus _ _ H).
replace (b * q1 + r1 - (b * q2 + r2))
 with (b*(q1-q2) - (r2-r1)) in H0 by ring.
assert (H1:=Zminus_eq _ _ H0).
destruct (Z_dec q1 q2).
 elim (Zlt_not_le (Zabs (r2 - r1)) (Zabs b)).
  apply Zabs_ind;  omega.
 rewrite <- H1.
 replace (Zabs b) with (1*(Zabs b)) by ring.
 rewrite Zabs_Zmult. 
 rewrite (Zmult_comm (Zabs b)).
 apply Zmult_le_compat_r; auto with *.
 change 1 with (Zsucc 0).
 apply Zlt_le_succ.
 destruct s; apply Zabs_ind; omega.
split; try assumption.
rewrite e in H1.
ring_simplify in H1.
omega.
Qed.

(** * Auxiliary lemmas about [Zdiv] and [Zmod] *)

Lemma Z_div_mod_eq : forall a b:Z, b > 0 -> a = b * Zdiv a b + Zmod a b.
Proof.
  unfold Zdiv, Zmod in |- *.
  intros a b Hb.
  generalize (Z_div_mod a b Hb).
  case Zdiv_eucl; tauto.
Qed.

Lemma Z_mod_lt : forall a b:Z, b > 0 -> 0 <= Zmod a b < b.
Proof.
  unfold Zmod in |- *.
  intros a b Hb.
  generalize (Z_div_mod a b Hb).
  case (Zdiv_eucl a b); tauto.
Qed.

Lemma Z_div_POS_ge0 :
  forall (b:Z) (a:positive), let (q, _) := Zdiv_eucl_POS a b in q >= 0.
Proof.
  simple induction a; cbv beta iota delta [Zdiv_eucl_POS] in |- *;
    fold Zdiv_eucl_POS in |- *; cbv zeta.
  intro p; case (Zdiv_eucl_POS p b).
  intros; case (Zgt_bool b (2 * z0 + 1)); intros; omega.
  intro p; case (Zdiv_eucl_POS p b).
  intros; case (Zgt_bool b (2 * z0)); intros; omega.
  case (Zge_bool b 2); simpl in |- *; omega.
Qed.

Lemma Z_div_ge0 : forall a b:Z, b > 0 -> a >= 0 -> Zdiv a b >= 0.
Proof.
  intros a b Hb; unfold Zdiv, Zdiv_eucl in |- *; case a; simpl in |- *; intros.
  case b; simpl in |- *; trivial.
  generalize Hb; case b; try trivial.
  auto with zarith.
  intros p0 Hp0; generalize (Z_div_POS_ge0 (Zpos p0) p).
  case (Zdiv_eucl_POS p (Zpos p0)); simpl in |- *; tauto.
  intros; discriminate.
  elim H; trivial.
Qed.

Lemma Z_div_lt : forall a b:Z, b >= 2 -> a > 0 -> Zdiv a b < a.
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

(** * Other lemmas (now using the syntax for [Zdiv] and [Zmod]). *)

Lemma Z_div_ge : forall a b c:Z, c > 0 -> a >= b -> a / c >= b / c.
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
  rewrite H0.
  rewrite H2.
  assert
    (c * (b / c) + b mod c - (c * (a / c) + a mod c) =
      c * (b / c - a / c) + b mod c - a mod c).
  ring.
  rewrite H3.
  assert (c * (b / c - a / c) >= c * 1).
  apply Zmult_ge_compat_l.
  omega.
  omega.
  assert (c * 1 = c).
  ring.
  omega.
Qed.

Lemma Z_div_le : forall a b c:Z, c > 0 -> a <= b -> a / c <= b / c.
Proof.
intros a b c H H0.
apply Zge_le.
apply Z_div_ge; auto with *.
Qed.

Lemma Z_mod_plus : forall a b c:Z, c > 0 -> (a + b * c) mod c = a mod c.
Proof.
  intros a b c cPos.
  generalize (Z_div_mod_eq a c cPos).
  generalize (Z_mod_lt a c cPos).
  generalize (Z_div_mod_eq (a + b * c) c cPos).
  generalize (Z_mod_lt (a + b * c) c cPos).
  intros.

  assert ((a + b * c) mod c - a mod c = c * (b + a / c - (a + b * c) / c)).
  replace ((a + b * c) mod c) with (a + b * c - c * ((a + b * c) / c)).
  replace (a mod c) with (a - c * (a / c)).
  ring.
  omega.
  omega.
  set (q := b + a / c - (a + b * c) / c) in *.
  apply (Zcase_sign q); intros.
  assert (c * q = 0).
  rewrite H4; ring.
  rewrite H5 in H3.
  omega.

  assert (c * q >= c).
  pattern c at 2 in |- *; replace c with (c * 1).
  apply Zmult_ge_compat_l; omega.
  ring.
  omega.

  assert (c * q <= - c).
  replace (- c) with (c * -1).
  apply Zmult_le_compat_l; omega.
  ring.
  omega.
Qed.

Lemma Z_div_plus : forall a b c:Z, c > 0 -> (a + b * c) / c = a / c + b.
Proof.
  intros a b c cPos.
  generalize (Z_div_mod_eq a c cPos).
  generalize (Z_mod_lt a c cPos).
  generalize (Z_div_mod_eq (a + b * c) c cPos).
  generalize (Z_mod_lt (a + b * c) c cPos).
  intros.
  apply Zmult_reg_l with c. omega.
  replace (c * ((a + b * c) / c)) with (a + b * c - (a + b * c) mod c).
  rewrite (Z_mod_plus a b c cPos).
  pattern a at 1 in |- *; rewrite H2.
  ring.
  pattern (a + b * c) at 1 in |- *; rewrite H0.
  ring.
Qed.

Lemma Zdiv_opp_opp : forall a b:Z, Zdiv (-a) (-b) = Zdiv a b.
Proof.
intros [|a|a] [|b|b];
 try reflexivity;
 unfold Zdiv;
 simpl;
 destruct (Zdiv_eucl_POS a (Zpos b)); destruct z0; try reflexivity.
Qed.

Lemma Z_div_mult : forall a b:Z, b > 0 -> a * b / b = a.
  intros; replace (a * b) with (0 + a * b); auto.
  rewrite Z_div_plus; auto.
Qed.

Lemma Zdiv_mult_cancel_r : forall (a b c:Z), 
 (c <> 0) -> (a*c/(b*c) = a/b).
Proof.
assert (X: forall a b c, b > 0 -> c > 0 -> a * c / (b * c) = a / b).
 intros a b c Hb Hc.
 assert (X:=Z_div_mod (a*c) (b*c)).
 assert (Y:=Z_div_mod a b Hb).
 unfold Zdiv.
 destruct (Zdiv_eucl (a*c) (b*c)).
 destruct (Zdiv_eucl a b).
 destruct Y as [Y0 Y1].
 rewrite Y0 in X.
 clear Y0.
 destruct X as [X0 X1].
  auto with *.
 replace ((b*z1 + z2)* c) with
  ((b*c)*z1 + z2*c) in X0 by ring.
 destruct (Zdiv_mod_unique (b*c) z1 z (z2*c) z0); try rewrite Zabs_eq; auto with *.
 split; auto with *.
 apply Zmult_lt_compat_r; auto with *.
intros a b c Hc.
destruct (Z_dec b 0) as [Hb|Hb].
 destruct Hb as [Hb|Hb];
  destruct (not_Zeq_inf _ _ Hc).
    rewrite <- (Zdiv_opp_opp a b).
    replace (b*c) with ((-b)*(-c)) by ring.
    replace (a*c) with ((-a)*(-c)) by ring.
    apply X; auto with *.
   rewrite <- (Zdiv_opp_opp a b).
   rewrite <- Zdiv_opp_opp.
   replace (-(b*c)) with ((-b)*c) by ring.
   replace (-(a*c)) with ((-a)*c) by ring.
   apply X; auto with *.
  rewrite <- Zdiv_opp_opp.
  replace (-(b*c)) with (b*(-c)) by ring.
  replace (-(a*c)) with (a*(-c)) by ring.
  apply X; auto with *.
 apply X; auto with *.
rewrite Hb.
destruct (a*c); destruct a; reflexivity.
Qed.

Lemma Z_mult_div_ge : forall a b:Z, b > 0 -> b * (a / b) <= a.
Proof.
  intros a b bPos.
  generalize (Z_div_mod_eq a _ bPos); intros.
  generalize (Z_mod_lt a _ bPos); intros.
  pattern a at 2 in |- *; rewrite H.
  omega.
Qed.

Lemma Z_mod_same : forall a:Z, a > 0 -> a mod a = 0.
Proof.
  intros a aPos.
  generalize (Z_mod_plus 0 1 a aPos).
  replace (0 + 1 * a) with a.
  intros.
  rewrite H.
  compute in |- *.
  trivial.
  ring.
Qed.

Lemma Z_div_same : forall a:Z, a > 0 -> a / a = 1.
Proof.
  intros a aPos.
  generalize (Z_div_plus 0 1 a aPos).
  replace (0 + 1 * a) with a.
  intros.
  rewrite H.
  compute in |- *.
  trivial.
  ring.
Qed.

Lemma Z_div_1 : forall z:Z, (z/1 = z)%Z.
Proof.
intros z.
set (z':=z).
unfold z' at 1.
replace z with (0 + z*1)%Z by ring.
rewrite (Z_div_plus 0 z 1);[reflexivity|constructor].
Qed.

Hint Resolve Z_div_1 : zarith.

Lemma Z_div_exact_1 : forall a b:Z, b > 0 -> a = b * (a / b) -> a mod b = 0.
  intros a b Hb; generalize (Z_div_mod a b Hb); unfold Zmod, Zdiv in |- *.
  case (Zdiv_eucl a b); intros q r; omega.
Qed.

Lemma Z_div_exact_2 : forall a b:Z, b > 0 -> a mod b = 0 -> a = b * (a / b).
  intros a b Hb; generalize (Z_div_mod a b Hb); unfold Zmod, Zdiv in |- *.
  case (Zdiv_eucl a b); intros q r; omega.
Qed.

Lemma Z_mod_zero_opp : forall a b:Z, b > 0 -> a mod b = 0 -> - a mod b = 0.
  intros a b Hb.
  intros.
  rewrite Z_div_exact_2 with a b; auto.
  replace (- (b * (a / b))) with (0 + - (a / b) * b).
  rewrite Z_mod_plus; auto.
  ring.
Qed.
