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
elim (Zis_gcd_bezout a b d H); intros.
elim H3; intros.
elim H4; intros.
apply Zdivide_intro with (u * q + v * q0).
rewrite <- H5.
replace (c * (u * a + v * b)) with (u * (c * a) + v * (c * b)).
rewrite H6; rewrite H7; ring.
ring.
Qed.

Lemma Zis_gcd_0_abs : forall b, 
 Zis_gcd 0 b (Zabs b) /\ Zabs b >= 0 /\ 0 = Zabs b * 0 /\ b = Zabs b * Zsgn b.
Proof.
intro b.
elim (Z_le_lt_eq_dec _ _ (Zabs_pos b)).
intros H0; split.
apply Zabs_ind.
intros; apply Zis_gcd_sym; apply Zis_gcd_0; auto.
intros; apply Zis_gcd_opp; apply Zis_gcd_0; auto.
repeat split; auto with zarith.
symmetry; apply Zabs_Zsgn.

intros H0; rewrite <- H0.
rewrite <- (Zabs_Zsgn b); rewrite <- H0; simpl in |- *.
split; [ apply Zis_gcd_0 | idtac ]; auto with zarith.
Qed.
  

(** We could obtain a [Zgcd] function via [euclid]. But we propose 
  here a more direct version of a [Zgcd], that can compute within Coq.
  For that, we use an explicit measure in [nat], and we proved later
  that using [2(d+1)] is enough, where  [d] is the number of binary digits 
  of the first argument. *)

Fixpoint Zgcdn (n:nat) : Z -> Z -> Z := fun a b => 
 match n with 
  | O => 1 (* arbitrary, since n should be big enough *)
  | S n => match a with 
     | Z0 => Zabs b
     | Zpos _ => Zgcdn n (Zmod b a) a
     | Zneg a => Zgcdn n (Zmod b (Zpos a)) (Zpos a)
     end
   end.

(* For technical reason, we don't use [Ndigit.Psize] but this 
   ad-hoc version: [Psize p = S (Psiz p)]. *)

Fixpoint Psiz (p:positive) : nat := 
  match p with 
    | xH => O
    | xI p => S (Psiz p) 
    | xO p => S (Psiz p)
  end.

Definition Zgcd_bound (a:Z) := match a with 
 | Z0 => S O
 | Zpos p => let n := Psiz p in S (S (n+n))
 | Zneg p => let n := Psiz p in S (S (n+n))
end.

Definition Zgcd a b := Zgcdn (Zgcd_bound a) a b.

(** A first obvious fact : [Zgcd a b] is positive. *)

Lemma Zgcdn_pos : forall n a b, 
  0 <= Zgcdn n a b.
Proof.
induction n.
simpl; auto with zarith.
destruct a; simpl; intros; auto with zarith; auto.
Qed.

Lemma Zgcd_pos : forall a b, 0 <= Zgcd a b.
Proof.
intros; unfold Zgcd; apply Zgcdn_pos; auto.
Qed.

(** We now prove that Zgcd is indeed a gcd. *)

(** 1) We prove a weaker & easier bound. *)

Lemma Zgcdn_linear_bound : forall n a b, 
 Zabs a < Z_of_nat n -> Zis_gcd a b (Zgcdn n a b).
Proof.
induction n.
simpl; intros.
elimtype False; generalize (Zabs_pos a); omega.
destruct a; intros; simpl; 
 [ generalize (Zis_gcd_0_abs b); intuition | | ]; 
 unfold Zmod; 
 generalize (Z_div_mod b (Zpos p) (refl_equal Gt));
 destruct (Zdiv_eucl b (Zpos p)) as (q,r);
 intros (H0,H1); 
 rewrite inj_S in H; simpl Zabs in H; 
 (assert (H2: Zabs r < Z_of_nat n) by
  rewrite Zabs_eq; auto with zarith);  
 assert (IH:=IHn r (Zpos p) H2); clear IHn; 
 simpl in IH |- *; 
 rewrite H0.
 apply Zis_gcd_for_euclid2; auto.
 apply Zis_gcd_minus; apply Zis_gcd_sym.
 apply Zis_gcd_for_euclid2; auto.
Qed.

(** 2) For Euclid's algorithm, the worst-case situation corresponds 
     to Fibonacci numbers. Let's define them: *)

Fixpoint fibonacci (n:nat) : Z := 
 match n with 
   | O => 1
   | S O => 1
   | S (S n as p) => fibonacci p + fibonacci n 
 end.

Lemma fibonacci_pos : forall n, 0 <= fibonacci n.
Proof.
cut (forall N n, (n<N)%nat -> 0<=fibonacci n).
eauto.
induction N.
inversion 1.
intros.
destruct n.
simpl; auto with zarith.
destruct n.
simpl; auto with zarith.
change (0 <= fibonacci (S n) + fibonacci n).
generalize (IHN n) (IHN (S n)); omega.
Qed.

Lemma fibonacci_incr : 
 forall n m, (n<=m)%nat -> fibonacci n <= fibonacci m.
Proof.
induction 1.
auto with zarith.
apply Zle_trans with (fibonacci m); auto.
clear.
destruct m.
simpl; auto with zarith.
change (fibonacci (S m) <= fibonacci (S m)+fibonacci m).
generalize (fibonacci_pos m); omega.
Qed.

(** 3) We prove that fibonacci numbers are indeed worst-case: 
   for a given number [n], if we reach a conclusion about [gcd(a,b)] in 
   exactly [n+1] loops, then [fibonacci (n+1)<=a /\ fibonacci(n+2)<=b] *)

Lemma Zgcdn_worst_is_fibonacci : forall n a b, 
 0 < a < b -> 
 Zis_gcd a b (Zgcdn (S n) a b) -> 
 Zgcdn n a b <> Zgcdn (S n) a b -> 
 fibonacci (S n) <= a /\ 
 fibonacci (S (S n)) <= b.
Proof.
induction n.
simpl; intros.
destruct a; omega.
intros.
destruct a; [simpl in *; omega| | destruct H; discriminate].
revert H1; revert H0.
set (m:=S n) in *; (assert (m=S n) by auto); clearbody m.
pattern m at 2; rewrite H0.
simpl Zgcdn.
unfold Zmod; generalize (Z_div_mod b (Zpos p) (refl_equal Gt)).
destruct (Zdiv_eucl b (Zpos p)) as (q,r).
intros (H1,H2).
destruct H2.
destruct (Zle_lt_or_eq _ _ H2).
generalize (IHn _ _ (conj H4 H3)).
intros H5 H6 H7. 
replace (fibonacci (S (S m))) with (fibonacci (S m) + fibonacci m) by auto.
assert (r = Zpos p * (-q) + b) by rewrite H1; ring.
destruct H5; auto.
pattern r at 1; rewrite H8.
apply Zis_gcd_sym.
apply Zis_gcd_for_euclid2; auto.
apply Zis_gcd_sym; auto.
split; auto.
rewrite H1.
apply Zplus_le_compat; auto.
apply Zle_trans with (Zpos p * 1); auto.
ring (Zpos p * 1); auto.
apply Zmult_le_compat_l.
destruct q.
omega.
assert (0 < Zpos p0) by compute; auto.
omega.
assert (Zpos p * Zneg p0 < 0) by compute; auto.
omega. 
compute; intros; discriminate.
(* r=0 *)
subst r.
simpl; rewrite H0.
intros.
simpl in H4.
simpl in H5.
destruct n.
simpl in H5.
simpl.
omega.
simpl in H5.
elim H5; auto.
Qed.

(** 3b) We reformulate the previous result in a more positive way. *)

Lemma Zgcdn_ok_before_fibonacci : forall n a b, 
 0 < a < b -> a < fibonacci (S n) ->
 Zis_gcd a b (Zgcdn n a b).
Proof.
destruct a; [ destruct 1; elimtype False; omega | | destruct 1; discriminate].
cut (forall k n b, 
         k = (S (nat_of_P p) - n)%nat -> 
         0 < Zpos p < b -> Zpos p < fibonacci (S n) -> 
         Zis_gcd (Zpos p) b (Zgcdn n (Zpos p) b)).
destruct 2; eauto.
clear n; induction k. 
intros.
assert (nat_of_P p < n)%nat by omega.
apply Zgcdn_linear_bound. 
simpl.
generalize (inj_le _ _ H2).
rewrite inj_S.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto.
omega.
intros.
generalize (Zgcdn_worst_is_fibonacci n (Zpos p) b H0); intros.
assert (Zis_gcd (Zpos p) b (Zgcdn (S n) (Zpos p) b)).
 apply IHk; auto.
 omega.
 replace (fibonacci (S (S n))) with (fibonacci (S n)+fibonacci n) by auto.
 generalize (fibonacci_pos n); omega.
replace (Zgcdn n (Zpos p) b) with (Zgcdn (S n) (Zpos p) b); auto.
generalize (H2 H3); clear H2 H3; omega.
Qed.

(** 4) The proposed bound leads to a fibonacci number that is big enough. *)

Lemma Zgcd_bound_fibonacci : 
  forall a, 0 < a -> a < fibonacci (Zgcd_bound a).
Proof.
destruct a; [omega| | intro H; discriminate].
intros _.
induction p.
simpl Zgcd_bound in *.
rewrite Zpos_xI.
rewrite plus_comm; simpl plus.
set (n:=S (Psiz p+Psiz p)) in *.
change (2*Zpos p+1 < 
 fibonacci (S n) + fibonacci n + fibonacci (S n)).
generalize (fibonacci_pos n).
omega.
simpl Zgcd_bound in *.
rewrite Zpos_xO.
rewrite plus_comm; simpl plus.
set (n:= S (Psiz p +Psiz p)) in *.
change (2*Zpos p < 
 fibonacci (S n) + fibonacci n + fibonacci (S n)).
generalize (fibonacci_pos n).
omega.
simpl; auto with zarith.
Qed.

(* 5) the end: we glue everything together and take care of 
   situations not corresponding to [0<a<b]. *)

Lemma Zgcd_is_gcd : 
  forall a b, Zis_gcd a b (Zgcd a b).
Proof.
unfold Zgcd; destruct a; intros.
simpl; generalize (Zis_gcd_0_abs b); intuition.
(*Zpos*)
generalize (Zgcd_bound_fibonacci (Zpos p)).
simpl Zgcd_bound.
set (n:=S (Psiz p+Psiz p)); (assert (n=S (Psiz p+Psiz p)) by auto); clearbody n.
simpl Zgcdn.
unfold Zmod.
generalize (Z_div_mod b (Zpos p) (refl_equal Gt)).
destruct (Zdiv_eucl b (Zpos p)) as (q,r).
intros (H1,H2) H3.
rewrite H1.
apply Zis_gcd_for_euclid2.
destruct H2.
destruct (Zle_lt_or_eq _ _ H0).
apply Zgcdn_ok_before_fibonacci; auto; omega.
subst r n; simpl.
apply Zis_gcd_sym; apply Zis_gcd_0.
(*Zneg*)
generalize (Zgcd_bound_fibonacci (Zpos p)).
simpl Zgcd_bound.
set (n:=S (Psiz p+Psiz p)); (assert (n=S (Psiz p+Psiz p)) by auto); clearbody n.
simpl Zgcdn.
unfold Zmod.
generalize (Z_div_mod b (Zpos p) (refl_equal Gt)).
destruct (Zdiv_eucl b (Zpos p)) as (q,r).
intros (H1,H2) H3.
rewrite H1.
apply Zis_gcd_minus.
apply Zis_gcd_sym.
apply Zis_gcd_for_euclid2.
destruct H2.
destruct (Zle_lt_or_eq _ _ H0).
apply Zgcdn_ok_before_fibonacci; auto; omega.
subst r n; simpl.
apply Zis_gcd_sym; apply Zis_gcd_0.
Qed.

(** A generalized gcd: it additionnally keeps track of the divisors. *)

Fixpoint Zggcdn (n:nat) : Z -> Z -> (Z*(Z*Z)) := fun a b => 
 match n with 
  | O => (1,(a,b))   (*(Zabs b,(0,Zsgn b))*)
  | S n => match a with 
     | Z0 => (Zabs b,(0,Zsgn b))
     | Zpos _ => 
               let (q,r) := Zdiv_eucl b a in   (* b = q*a+r *)
               let (g,p) := Zggcdn n r a in 
               let (rr,aa) := p in        (* r = g *rr /\ a = g * aa *)
               (g,(aa,q*aa+rr))
     | Zneg a => 
               let (q,r) := Zdiv_eucl b (Zpos a) in  (* b = q*(-a)+r *)
               let (g,p) := Zggcdn n r (Zpos a) in 
               let (rr,aa) := p in         (* r = g*rr /\ (-a) = g * aa *)  
               (g,(-aa,q*aa+rr))
     end
   end.

Definition Zggcd a b : Z * (Z * Z) := Zggcdn (Zgcd_bound a) a b.

(** The first component of [Zggcd] is [Zgcd] *) 

Lemma Zggcdn_gcdn : forall n a b, 
 fst (Zggcdn n a b) = Zgcdn n a b.
Proof.
induction n; simpl; auto.
destruct a; unfold Zmod; simpl; intros; auto; 
 destruct (Zdiv_eucl b (Zpos p)) as (q,r); 
 rewrite <- IHn; 
 destruct (Zggcdn n r (Zpos p)) as (g,(rr,aa)); simpl; auto.
Qed.

Lemma Zggcd_gcdn : forall a b, fst (Zggcd a b) = Zgcd a b.
Proof.
intros; unfold Zggcd, Zgcd; apply Zggcdn_gcdn; auto.
Qed.

(** [Zggcd] always returns divisors that are coherent with its 
 first output. *)

Lemma Zggcdn_correct_divisors : forall n a b, 
  let (g,p) := Zggcdn n a b in 
  let (aa,bb):=p in 
  a=g*aa /\ b=g*bb.
Proof.
induction n.
simpl.
split; [destruct a|destruct b]; auto.
intros.
simpl.
destruct a.
rewrite Zmult_comm; simpl.
split; auto.
symmetry; apply Zabs_Zsgn.
generalize (Z_div_mod b (Zpos p)); 
destruct (Zdiv_eucl b (Zpos p)) as (q,r).
generalize (IHn r (Zpos p)); 
destruct (Zggcdn n r (Zpos p)) as (g,(rr,aa)).
intuition.
destruct H0.
compute; auto.
rewrite H; rewrite H1; rewrite H2; ring.
generalize (Z_div_mod b (Zpos p)); 
destruct (Zdiv_eucl b (Zpos p)) as (q,r).
destruct 1.
compute; auto.
generalize (IHn r (Zpos p)); 
destruct (Zggcdn n r (Zpos p)) as (g,(rr,aa)).
intuition.
destruct H0.
replace (Zneg p) with (-Zpos p) by compute; auto.
rewrite H4; ring.
rewrite H; rewrite H4; rewrite H0; ring.
Qed.

Lemma Zggcd_correct_divisors : forall a b, 
  let (g,p) := Zggcd a b in 
  let (aa,bb):=p in 
  a=g*aa /\ b=g*bb.
Proof.
unfold Zggcd; intros; apply Zggcdn_correct_divisors; auto.
Qed.
 
(** Due to the use of an explicit measure, the extraction of [Zgcd] 
  isn't optimal. We propose here another version [Zgcd_spec] that 
  doesn't suffer from this problem (but doesn't compute in Coq). *)

Definition Zgcd_spec_pos :
  forall a:Z,
    0 <= a -> forall b:Z, {g : Z | 0 <= a -> Zis_gcd a b g /\ g >= 0}.
Proof.
intros a Ha.
apply
 (Zlt_0_rec
    (fun a:Z => forall b:Z, {g : Z | 0 <= a -> Zis_gcd a b g /\ g >= 0}));
 try assumption.
intro x; case x.
intros _ _ b; exists (Zabs b).
generalize (Zis_gcd_0_abs b); intuition.
  
intros p Hrec _ b.
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

intros p _ H b.
elim H; auto.
Defined.

Definition Zgcd_spec : forall a b:Z, {g : Z | Zis_gcd a b g /\ g >= 0}.
Proof.
intros a; case (Z_gt_le_dec 0 a).
intros; assert (0 <= - a).
omega.
elim (Zgcd_spec_pos (- a) H b); intros g Hgkl.
exists g.
intuition.
intros Ha b; elim (Zgcd_spec_pos a Ha b); intros g; exists g; intuition.
Defined.

(** A last version aimed at extraction that also returns the divisors. *)

Definition Zggcd_spec_pos :
  forall a:Z,
    0 <= a -> forall b:Z, {p : Z*(Z*Z) | let (g,p):=p in let (aa,bb):=p in 
                                       0 <= a -> Zis_gcd a b g /\ g >= 0 /\ a=g*aa /\ b=g*bb}.
Proof.
intros a Ha.
pattern a; apply Zlt_0_rec; try assumption.
intro x; case x.
intros _ _ b; exists (Zabs b,(0,Zsgn b)).
intros _; apply Zis_gcd_0_abs.
  
intros p Hrec _ b.
generalize (Z_div_mod b (Zpos p)).
case (Zdiv_eucl b (Zpos p)); intros q r Hqr.
elim Hqr; clear Hqr; intros; auto with zarith.
destruct (Hrec r H0 (Zpos p)) as ((g,(rr,pp)),Hgkl).
destruct H0.
destruct (Hgkl H0) as (H3,(H4,(H5,H6))).
exists (g,(pp,pp*q+rr)); intros.
split; auto.
rewrite H.
apply Zis_gcd_for_euclid2; auto.
repeat split; auto.
rewrite H; rewrite H6; rewrite H5; ring.

intros p _ H b.
elim H; auto.
Defined.

Definition Zggcd_spec : 
 forall a b:Z, {p : Z*(Z*Z) |  let (g,p):=p in let (aa,bb):=p in 
                                          Zis_gcd a b g /\ g >= 0 /\ a=g*aa /\ b=g*bb}.
Proof.
intros a; case (Z_gt_le_dec 0 a).
intros; assert (0 <= - a).
omega.
destruct (Zggcd_spec_pos (- a) H b) as ((g,(aa,bb)),Hgkl).
exists (g,(-aa,bb)).
intuition.
rewrite <- Zopp_mult_distr_r.
rewrite <- H2; auto with zarith.
intros Ha b; elim (Zggcd_spec_pos a Ha b); intros p; exists p.
 repeat destruct p; intuition.
Defined.

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

