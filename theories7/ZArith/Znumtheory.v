(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require ZArith_base.
Require ZArithRing.
Require Zcomplements.
Require Zdiv.
V7only [Import Z_scope.].
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

Inductive Zdivide [a,b:Z] : Prop := 
  Zdivide_intro : (q:Z) `b = q * a` -> (Zdivide a b).

(** Syntax for divisibility *)

Notation "( a | b )" := (Zdivide a b) 
 (at level 0, a,b at level 10) : Z_scope
 V8only "( a | b )" (at level 0).

(** Results concerning divisibility*)

Lemma Zdivide_refl : (a:Z) (a|a).
Proof.
Intros; Apply Zdivide_intro with `1`; Ring.
Save.

Lemma Zone_divide : (a:Z) (1|a).
Proof.
Intros; Apply Zdivide_intro with `a`; Ring.
Save.

Lemma Zdivide_0 : (a:Z) (a|0).
Proof.
Intros; Apply Zdivide_intro with `0`; Ring.
Save.

Hints Resolve Zdivide_refl Zone_divide Zdivide_0 : zarith.

Lemma Zdivide_mult_left : (a,b,c:Z) (a|b) -> (`c*a`|`c*b`).
Proof.
Induction 1; Intros; Apply Zdivide_intro with q.
Rewrite H0; Ring.
Save.

Lemma Zdivide_mult_right : (a,b,c:Z) (a|b) -> (`a*c`|`b*c`).
Proof.
Intros a b c; Rewrite (Zmult_sym a c); Rewrite (Zmult_sym b c).
Apply Zdivide_mult_left; Trivial.
Save.

Hints Resolve Zdivide_mult_left Zdivide_mult_right : zarith.

Lemma Zdivide_plus : (a,b,c:Z) (a|b) -> (a|c) -> (a|`b+c`).
Proof.
Induction 1; Intros q Hq; Induction 1; Intros q' Hq'.
Apply Zdivide_intro with `q+q'`.
Rewrite Hq; Rewrite Hq'; Ring.
Save.

Lemma Zdivide_opp : (a,b:Z) (a|b) -> (a|`-b`).
Proof.
Induction 1; Intros; Apply Zdivide_intro with `-q`.
Rewrite H0; Ring.
Save.

Lemma Zdivide_opp_rev : (a,b:Z) (a|`-b`) -> (a| b).
Proof.
Intros; Replace b with `-(-b)`. Apply Zdivide_opp; Trivial. Ring.
Save.

Lemma Zdivide_opp_left : (a,b:Z) (a|b) -> (`-a`|b).
Proof.
Induction 1; Intros; Apply Zdivide_intro with `-q`.
Rewrite H0; Ring.
Save.

Lemma Zdivide_opp_left_rev : (a,b:Z) (`-a`|b) -> (a|b).
Proof.
Intros; Replace a with `-(-a)`. Apply Zdivide_opp_left; Trivial. Ring.
Save.

Lemma Zdivide_minus : (a,b,c:Z) (a|b) -> (a|c) -> (a|`b-c`).
Proof.
Induction 1; Intros q Hq; Induction 1; Intros q' Hq'.
Apply Zdivide_intro with `q-q'`.
Rewrite Hq; Rewrite Hq'; Ring.
Save.

Lemma Zdivide_left : (a,b,c:Z) (a|b) -> (a|`b*c`).
Proof.
Induction 1; Intros q Hq; Apply Zdivide_intro with `q*c`.
Rewrite Hq; Ring.
Save.

Lemma Zdivide_right : (a,b,c:Z) (a|c) -> (a|`b*c`).
Proof.
Induction 1; Intros q Hq; Apply Zdivide_intro with `q*b`.
Rewrite Hq; Ring.
Save.

Lemma Zdivide_a_ab : (a,b:Z) (a|`a*b`).
Proof.
Intros; Apply Zdivide_intro with b; Ring.
Save.

Lemma Zdivide_a_ba : (a,b:Z) (a|`b*a`).
Proof.
Intros; Apply Zdivide_intro with b; Ring.
Save.

Hints Resolve Zdivide_plus Zdivide_opp Zdivide_opp_rev
              Zdivide_opp_left Zdivide_opp_left_rev
              Zdivide_minus Zdivide_left Zdivide_right
              Zdivide_a_ab Zdivide_a_ba : zarith.

(** Auxiliary result. *)

Lemma Zmult_one : 
 (x,y:Z) `x>=0` -> `x*y=1` -> `x=1`.
Proof.
Intros x y H H0; NewDestruct (Zmult_1_inversion_l ? ? H0) as [Hpos|Hneg].
  Assumption.
  Rewrite Hneg in H; Simpl in H.
  Contradiction (Zle_not_lt `0` `-1`).
    Apply Zge_le; Assumption.
    Apply NEG_lt_ZERO.
Save.

(** Only [1] and [-1] divide [1]. *)

Lemma Zdivide_1 : (x:Z) (x|1) -> `x=1` \/ `x=-1`.
Proof.
Induction 1; Intros.
Elim (Z_lt_ge_dec `0` x); [Left|Right].
Apply Zmult_one with q; Auto with zarith; Rewrite H0; Ring.
Assert `(-x) = 1`; Auto with zarith.
Apply Zmult_one with (-q); Auto with zarith; Rewrite H0; Ring.
Save.

(** If [a] divides [b] and [b] divides [a] then [a] is [b] or [-b]. *)

Lemma Zdivide_antisym : (a,b:Z) (a|b) -> (b|a) -> `a=b` \/ `a=-b`.
Proof.
Induction 1; Intros.
Inversion H1.
Rewrite H0 in H2; Clear H H1.
Case (Z_zerop a); Intro.
Left; Rewrite H0; Rewrite e; Ring.
Assert Hqq0: `q0*q = 1`.
Apply Zmult_reg_left with a.
Assumption.
Ring.
Pattern 2 a; Rewrite H2; Ring.
Assert (q|1).
Rewrite <- Hqq0; Auto with zarith.
Elim (Zdivide_1 q H); Intros.
Rewrite H1 in H0; Left; Omega.
Rewrite H1 in H0; Right; Omega.
Save.

(** If [a] divides [b] and [b<>0] then [|a| <= |b|]. *)

Lemma Zdivide_bounds : (a,b:Z) (a|b) -> `b<>0` -> `|a| <= |b|`.
Proof.
Induction 1; Intros.
Assert `|b|=|q|*|a|`.
 Subst; Apply Zabs_Zmult.
Rewrite H2.
Assert H3 := (Zabs_pos q).
Assert H4 := (Zabs_pos a).
Assert `|q|*|a|>=1*|a|`; Auto with zarith.
Apply Zge_Zmult_pos_compat; Auto with zarith.
Elim (Z_lt_ge_dec `|q|` `1`); [ Intros | Auto with zarith ].
Assert `|q|=0`.
 Omega.
Assert `q=0`.
 Rewrite <- (Zabs_Zsgn q).
Rewrite H5; Auto with zarith.
Subst q; Omega.
Save.

(** * Greatest common divisor (gcd). *)
   
(** There is no unicity of the gcd; hence we define the predicate [gcd a b d] 
     expressing that [d] is a gcd of [a] and [b]. 
     (We show later that the [gcd] is actually unique if we discard its sign.) *)

Inductive gcd [a,b,d:Z] : Prop :=
  gcd_intro : 
    (d|a) -> (d|b) -> ((x:Z) (x|a) -> (x|b) -> (x|d)) -> (gcd a b d).

(** Trivial properties of [gcd] *)

Lemma gcd_sym : (a,b,d:Z)(gcd a b d) -> (gcd b a d).
Proof.
Induction 1; Constructor; Intuition.
Save.

Lemma gcd_0 : (a:Z)(gcd a `0` a).
Proof.
Constructor; Auto with zarith.
Save.

Lemma gcd_minus :(a,b,d:Z)(gcd a `-b` d) -> (gcd b a d).
Proof.
Induction 1; Constructor; Intuition.
Save.

Lemma gcd_opp :(a,b,d:Z)(gcd a b d) -> (gcd b a `-d`).
Proof.
Induction 1; Constructor; Intuition.
Save.

Hints Resolve gcd_sym gcd_0 gcd_minus gcd_opp : zarith.

(** * Extended Euclid algorithm. *)

(** Euclid's algorithm to compute the [gcd] mainly relies on
    the following property. *)

Lemma gcd_for_euclid :
  (a,b,d,q:Z) (gcd b `a-q*b` d) -> (gcd a b d).
Proof.
Induction 1; Constructor; Intuition.
Replace a with `a-q*b+q*b`. Auto with zarith. Ring.
Save.

Lemma gcd_for_euclid2 :
  (b,d,q,r:Z) (gcd r b d) -> (gcd b `b*q+r` d).
Proof.
Induction 1; Constructor; Intuition.
Apply H2; Auto.
Replace r with `b*q+r-b*q`. Auto with zarith. Ring.
Save.

(** We implement the extended version of Euclid's algorithm,
    i.e. the one computing Bezout's coefficients as it computes
    the [gcd]. We follow the algorithm given in Knuth's
    "Art of Computer Programming", vol 2, page 325. *)

Section extended_euclid_algorithm.

Variable a,b : Z.

(** The specification of Euclid's algorithm is the existence of
    [u], [v] and [d] such that [ua+vb=d] and [(gcd a b d)]. *)

Inductive Euclid : Set :=
  Euclid_intro : 
    (u,v,d:Z) `u*a+v*b=d` -> (gcd a b d) -> Euclid.

(** The recursive part of Euclid's algorithm uses well-founded
    recursion of non-negative integers. It maintains 6 integers
    [u1,u2,u3,v1,v2,v3] such that the following invariant holds:
    [u1*a+u2*b=u3] and [v1*a+v2*b=v3] and [gcd(u2,v3)=gcd(a,b)]. 
    *)

Lemma euclid_rec :
  (v3:Z) `0 <= v3` -> (u1,u2,u3,v1,v2:Z) `u1*a+u2*b=u3` -> `v1*a+v2*b=v3` -> 
  ((d:Z)(gcd u3 v3 d) -> (gcd a b d)) -> Euclid.
Proof.
Intros v3 Hv3; Generalize Hv3; Pattern v3.
Apply Z_lt_rec.
Clear v3 Hv3; Intros.
Elim (Z_zerop x); Intro.
Apply Euclid_intro with u:=u1 v:=u2 d:=u3.
Assumption.
Apply H2.
Rewrite a0; Auto with zarith.
LetTac q := (Zdiv u3 x).
Assert Hq: `0 <= u3-q*x < x`.
Replace `u3-q*x` with `u3%x`.
Apply Z_mod_lt; Omega.
Assert xpos : `x > 0`. Omega.
Generalize (Z_div_mod_eq u3 x xpos). 
Unfold q. 
Intro eq; Pattern 2 u3; Rewrite eq; Ring.
Apply (H `u3-q*x` Hq (proj1 ? ? Hq) v1 v2 x `u1-q*v1` `u2-q*v2`).
Tauto.
Replace `(u1-q*v1)*a+(u2-q*v2)*b` with `(u1*a+u2*b)-q*(v1*a+v2*b)`.
Rewrite H0; Rewrite H1; Trivial.
Ring.
Intros; Apply H2.
Apply gcd_for_euclid with q; Assumption.
Assumption.
Save.

(** We get Euclid's algorithm by applying [euclid_rec] on
    [1,0,a,0,1,b] when [b>=0] and [1,0,a,0,-1,-b] when [b<0]. *)

Lemma euclid : Euclid.
Proof.
Case (Z_le_gt_dec `0` b); Intro.
Intros; Apply euclid_rec with u1:=`1` u2:=`0` u3:=a
                              v1:=`0` v2:=`1` v3:=b;
Auto with zarith; Ring.
Intros; Apply euclid_rec with u1:=`1` u2:=`0` u3:=a
                              v1:=`0` v2:=`-1` v3:=`-b`;
Auto with zarith; Try Ring.
Save.

End extended_euclid_algorithm.

Theorem gcd_uniqueness_apart_sign :
  (a,b,d,d':Z) (gcd a b d) -> (gcd a b d') -> `d = d'` \/ `d = -d'`.
Proof.
Induction 1.
Intros H1 H2 H3; Induction 1; Intros.
Generalize (H3 d' H4 H5); Intro Hd'd.
Generalize (H6 d H1 H2); Intro Hdd'.
Exact (Zdivide_antisym d d' Hdd' Hd'd).
Save.

(** * Bezout's coefficients *)

Inductive Bezout [a,b,d:Z] : Prop := 
  Bezout_intro : (u,v:Z) `u*a + v*b = d` -> (Bezout a b d).

(** Existence of Bezout's coefficients for the [gcd] of [a] and [b] *)

Lemma gcd_bezout : (a,b,d:Z) (gcd a b d) -> (Bezout a b d).
Proof.
Intros a b d Hgcd.
Elim (euclid a b); Intros u v d0 e g.
Generalize (gcd_uniqueness_apart_sign a b d d0 Hgcd g).
Intro H; Elim H; Clear H; Intros.
Apply Bezout_intro with u v.
Rewrite H; Assumption.
Apply Bezout_intro with `-u` `-v`.
Rewrite H; Rewrite <- e; Ring.
Save.

(** gcd of [ca] and [cb] is [c gcd(a,b)]. *)

Lemma gcd_mult : (a,b,c,d:Z) (gcd a b d) -> (gcd `c*a` `c*b` `c*d`).
Proof.
Intros a b c d; Induction 1; Constructor; Intuition.
Elim (gcd_bezout a b d H); Intros.
Elim H3; Intros.
Elim H4; Intros.
Apply Zdivide_intro with `u*q+v*q0`.
Rewrite <- H5.
Replace `c*(u*a+v*b)` with `u*(c*a)+v*(c*b)`.
Rewrite H6; Rewrite H7; Ring.
Ring.
Save.

(** We could obtain a [Zgcd] function via [euclid]. But we propose 
  here a more direct version of a [Zgcd], with better extraction 
  (no bezout coeffs). *)

Definition Zgcd_pos : (a:Z)`0<=a` -> (b:Z) 
 { g:Z | `0<=a` -> (gcd a b g) /\ `g>=0` }.
Proof.
Intros a Ha.
Apply (Z_lt_rec [a:Z](b:Z) { g:Z | `0<=a` -> (gcd a b g) /\`g>=0` }); Try Assumption.
Intro x; Case x.
Intros _ b; Exists (Zabs b).
  Elim (Z_le_lt_eq_dec ? ? (Zabs_pos b)).
    Intros H0; Split.
    Apply Zabs_ind.
    Intros; Apply gcd_sym; Apply gcd_0; Auto.
    Intros; Apply gcd_opp; Apply gcd_0; Auto.
    Auto with zarith.
    
    Intros H0;  Rewrite <- H0.
    Rewrite <- (Zabs_Zsgn b); Rewrite <- H0; Simpl.
    Split; [Apply gcd_0|Idtac];Auto with zarith.
  
Intros p Hrec b.
Generalize (Z_div_mod b (POS p)).
Case (Zdiv_eucl b (POS p)); Intros q r Hqr.
Elim Hqr; Clear Hqr; Intros; Auto with zarith.
Elim (Hrec r H0 (POS p)); Intros g Hgkl.
Inversion_clear H0.
Elim (Hgkl H1); Clear Hgkl; Intros H3 H4.
Exists g; Intros.
Split; Auto.
Rewrite H.
Apply gcd_for_euclid2; Auto.

Intros p Hrec b.
Exists `0`; Intros.
Elim H; Auto.
Defined.

Definition Zgcd_spec : (a,b:Z){ g : Z | (gcd a b g) /\ `g>=0` }.
Proof.
Intros a; Case (Z_gt_le_dec `0` a).
Intros; Assert `0 <= -a`.
Omega.
Elim (Zgcd_pos `-a` H b); Intros g Hgkl.
Exists g.
Intuition.
Intros Ha b; Elim (Zgcd_pos a Ha b); Intros g; Exists g; Intuition.
Defined.

Definition Zgcd := [a,b:Z](let (g,_) = (Zgcd_spec a b) in g).

Lemma Zgcd_is_pos : (a,b:Z)`(Zgcd a b) >=0`.
Intros a b; Unfold Zgcd; Case (Zgcd_spec a b); Tauto.
Qed.

Lemma Zgcd_is_gcd : (a,b:Z)(gcd a b (Zgcd a b)).
Intros a b; Unfold Zgcd; Case (Zgcd_spec a b); Tauto.
Qed.

(** * Relative primality *)

Definition rel_prime [a,b:Z] : Prop := (gcd a b `1`).

(** Bezout's theorem: [a] and [b] are relatively prime if and
    only if there exist [u] and [v] such that [ua+vb = 1]. *)

Lemma rel_prime_bezout : 
  (a,b:Z) (rel_prime a b) -> (Bezout a b `1`).
Proof.
Intros a b; Exact (gcd_bezout a b `1`).
Save.

Lemma bezout_rel_prime :
  (a,b:Z) (Bezout a b `1`) -> (rel_prime a b).
Proof.
Induction 1; Constructor; Auto with zarith.
Intros. Rewrite <- H0; Auto with zarith.
Save.

(** Gauss's theorem: if [a] divides [bc] and if [a] and [b] are
    relatively prime, then [a] divides [c]. *)

Theorem Gauss : (a,b,c:Z) (a |`b*c`) -> (rel_prime a b) -> (a | c).
Proof.
Intros. Elim (rel_prime_bezout a b H0); Intros.
Replace c with `c*1`; [ Idtac | Ring ].
Rewrite <- H1.
Replace `c*(u*a+v*b)` with `(c*u)*a + v*(b*c)`; [ EAuto with zarith | Ring ].
Save.

(** If [a] is relatively prime to [b] and [c], then it is to [bc] *)

Lemma rel_prime_mult : 
  (a,b,c:Z) (rel_prime a b) -> (rel_prime a c) -> (rel_prime a `b*c`).
Proof.
Intros a b c Hb Hc.
Elim (rel_prime_bezout a b Hb); Intros.
Elim (rel_prime_bezout a c Hc); Intros.
Apply bezout_rel_prime.
Apply Bezout_intro with u:=`u*u0*a+v0*c*u+u0*v*b` v:=`v*v0`.
Rewrite <- H.
Replace `u*a+v*b` with `(u*a+v*b) * 1`; [ Idtac | Ring ].
Rewrite <- H0.
Ring.
Save.

Lemma rel_prime_cross_prod :
  (a,b,c,d:Z) (rel_prime a b) -> (rel_prime c d) -> `b>0` -> `d>0` -> 
  `a*d = b*c` -> (a=c /\ b=d).
Proof.
Intros a b c d; Intros.
Elim (Zdivide_antisym b d).
Split; Auto with zarith.
Rewrite H4 in H3.
Rewrite Zmult_sym in H3.
Apply Zmult_reg_left with d; Auto with zarith.
Intros; Omega.
Apply Gauss with a.
Rewrite H3.
Auto with zarith.
Red; Auto with zarith.
Apply Gauss with c.
Rewrite Zmult_sym.
Rewrite <- H3.
Auto with zarith.
Red; Auto with zarith.
Save.

(** After factorization by a gcd, the original numbers are relatively prime. *)

Lemma gcd_rel_prime : 
 (a,b,g:Z)`b>0` -> `g>=0`-> (gcd a b g) -> (rel_prime `a/g` `b/g`).
Intros a b g; Intros.
Assert `g <> 0`.
 Intro.
 Elim H1; Intros. 
 Elim H4; Intros.
 Rewrite H2 in H6; Subst b; Omega.
Unfold rel_prime.
Elim (Zgcd_spec `a/g` `b/g`); Intros g' (H3,H4).
Assert H5 := (gcd_mult ? ? g ? H3).
Rewrite <- Z_div_exact_2 in H5; Auto with zarith.
Rewrite <- Z_div_exact_2 in H5; Auto with zarith.
Elim (gcd_uniqueness_apart_sign ? ? ? ? H1 H5).
Intros; Rewrite (!Zmult_reg_left `1` g' g); Auto with zarith.
Intros; Rewrite (!Zmult_reg_left `1` `-g'` g); Auto with zarith.
Pattern 1 g; Rewrite H6; Ring.

Elim H1; Intros.
Elim H7; Intros.
Rewrite H9.
Replace `q*g` with `0+q*g`.
Rewrite Z_mod_plus.
Compute; Auto.
Omega.
Ring.

Elim H1; Intros.
Elim H6; Intros.
Rewrite H9.
Replace `q*g` with `0+q*g`.
Rewrite Z_mod_plus.
Compute; Auto.
Omega.
Ring.
Save.

(** * Primality *)

Inductive prime [p:Z] : Prop := 
  prime_intro : 
   `1 < p` -> ((n:Z) `1 <= n < p` -> (rel_prime n p)) -> (prime p).

(** The sole divisors of a prime number [p] are [-1], [1], [p] and [-p]. *)

Lemma prime_divisors : 
  (p:Z) (prime p) -> 
  (a:Z) (a|p) -> `a = -1` \/ `a = 1` \/ a = p \/ `a = -p`.
Proof.
Induction 1; Intros.
Assert `a = (-p)`\/`-p<a< -1`\/`a = -1`\/`a=0`\/`a = 1`\/`1<a<p`\/`a = p`.
Assert `|a| <= |p|`. Apply Zdivide_bounds; [ Assumption | Omega ].
Generalize H3. 
Pattern `|a|`; Apply Zabs_ind; Pattern `|p|`; Apply Zabs_ind; Intros; Omega.
Intuition Idtac.
(* -p < a < -1 *)
Absurd (rel_prime `-a` p); Intuition.
Inversion H3.
Assert (`-a` | `-a`); Auto with zarith.
Assert (`-a` | p); Auto with zarith.
Generalize (H8 `-a` H9 H10); Intuition Idtac.
Generalize (Zdivide_1 `-a` H11); Intuition.
(* a = 0 *)
Inversion H2. Subst a; Omega.
(* 1 < a < p *)
Absurd (rel_prime a p); Intuition.
Inversion H3.
Assert (a | a); Auto with zarith.
Assert (a | p); Auto with zarith.
Generalize (H8 a H9 H10); Intuition Idtac.
Generalize (Zdivide_1 a H11); Intuition.
Save.

(** A prime number is relatively prime with any number it does not divide *)

Lemma prime_rel_prime : 
  (p:Z) (prime p) -> (a:Z) ~ (p|a) -> (rel_prime p a).
Proof.
Induction 1; Intros.
Constructor; Intuition.
Elim (prime_divisors p H x H3); Intuition; Subst; Auto with zarith.
Absurd (p | a); Auto with zarith.
Absurd (p | a); Intuition.
Save.

Hints Resolve prime_rel_prime : zarith.

(** [Zdivide] can be expressed using [Zmod]. *)

Lemma Zmod_Zdivide : (a,b:Z) `b>0` -> `a%b = 0` -> (b|a).
Intros a b H H0.
Apply Zdivide_intro with `(a/b)`.
Pattern 1 a; Rewrite (Z_div_mod_eq a b H).
Rewrite H0; Ring.
Save.

Lemma Zdivide_Zmod : (a,b:Z) `b>0` -> (b|a) -> `a%b = 0`.
Intros a b; Destruct 2; Intros; Subst.
Change `q*b` with `0+q*b`.
Rewrite Z_mod_plus; Auto.
Save.

(** [Zdivide] is hence decidable *)

Lemma Zdivide_dec : (a,b:Z) { (a|b) } + { ~ (a|b) }.
Proof.
Intros a b; Elim (Ztrichotomy_inf a `0`).
(* a<0 *)
Intros H; Elim H; Intros. 
Case (Z_eq_dec `b%(-a)` `0`).
Left; Apply Zdivide_opp_left_rev; Apply Zmod_Zdivide; Auto with zarith.
Intro H1; Right; Intro; Elim H1; Apply Zdivide_Zmod; Auto with zarith.
(* a=0 *)
Case (Z_eq_dec b `0`); Intro.
Left; Subst; Auto with zarith.
Right; Subst; Intro H0; Inversion H0; Omega.
(* a>0 *)
Intro H; Case (Z_eq_dec `b%a` `0`).
Left; Apply Zmod_Zdivide; Auto with zarith.
Intro H1; Right; Intro; Elim H1; Apply Zdivide_Zmod; Auto with zarith.
Save.

(** If a prime [p] divides [ab] then it divides either [a] or [b] *)

Lemma prime_mult : 
  (p:Z) (prime p) -> (a,b:Z) (p | `a*b`) -> (p | a) \/ (p | b).
Proof.
Intro p; Induction 1; Intros.
Case (Zdivide_dec p a); Intuition.
Right; Apply Gauss with a; Auto with zarith.
Save.


