(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Export Bool.
Require Export Setoid.

Set Implicit Arguments.

Section Setoid_rings.

Variable A : Type.
Variable Aequiv : A -> A -> Prop.

Infix Local "==" Aequiv (at level 5, no associativity).

Variable S : (Setoid_Theory A Aequiv).

Add Setoid A Aequiv S.

Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
Variable Aopp : A -> A.
Variable Aeq : A -> A -> bool.

Infix 4 "+" Aplus V8only 50 (left associativity).
Infix 4 "*" Amult V8only 40 (left associativity).
Notation "0" := Azero.
Notation "1" := Aone.
Notation "- x" := (Aopp x) (at level 0) V8only.

Variable plus_morph : (a,a0,a1,a2:A) a == a0 -> a1 == a2 -> a+a1 == a0+a2.
Variable mult_morph : (a,a0,a1,a2:A) a == a0 -> a1 == a2 -> a*a1 == a0*a2.
Variable opp_morph : (a,a0:A) a == a0 -> -a == -a0.

Add Morphism Aplus : Aplus_ext.
Exact plus_morph.
Save.

Add Morphism Amult : Amult_ext.
Exact mult_morph.
Save.

Add Morphism Aopp : Aopp_ext.
Exact opp_morph.
Save.

Section Theory_of_semi_setoid_rings.

Record Semi_Setoid_Ring_Theory : Prop :=
{ SSR_plus_sym  : (n,m:A) n + m == m + n;
  SSR_plus_assoc : (n,m,p:A) n + (m + p) == (n + m) + p;
  SSR_mult_sym : (n,m:A) n*m == m*n;
  SSR_mult_assoc : (n,m,p:A) n*(m*p) == (n*m)*p;
  SSR_plus_zero_left :(n:A) 0 + n == n;
  SSR_mult_one_left : (n:A) 1*n == n;
  SSR_mult_zero_left : (n:A) 0*n == 0;
  SSR_distr_left : (n,m,p:A) (n + m)*p == n*p + m*p;
  SSR_plus_reg_left : (n,m,p:A)n + m == n + p -> m == p;
  SSR_eq_prop : (x,y:A) (Is_true (Aeq x y)) -> x == y
}.

Variable T : Semi_Setoid_Ring_Theory.

Local plus_sym  := (SSR_plus_sym T).
Local plus_assoc := (SSR_plus_assoc T).
Local mult_sym  := ( SSR_mult_sym T).
Local mult_assoc := (SSR_mult_assoc T).
Local plus_zero_left := (SSR_plus_zero_left T).
Local mult_one_left := (SSR_mult_one_left T). 
Local mult_zero_left := (SSR_mult_zero_left T).
Local distr_left := (SSR_distr_left T).
Local plus_reg_left := (SSR_plus_reg_left T).
Local equiv_refl := (Seq_refl A Aequiv S).
Local equiv_sym := (Seq_sym A Aequiv S).
Local equiv_trans := (Seq_trans A Aequiv S).

Hints Resolve plus_sym plus_assoc mult_sym mult_assoc
  plus_zero_left mult_one_left mult_zero_left distr_left
  plus_reg_left equiv_refl (*equiv_sym*).
Hints Immediate equiv_sym.

(* Lemmas whose form is x=y are also provided in form y=x because
  Auto does not symmetry *) 
Lemma SSR_mult_assoc2 : (n,m,p:A) (n * m) * p == n * (m * p).
Auto. Save.

Lemma SSR_plus_assoc2 : (n,m,p:A) (n + m) + p == n + (m + p).
Auto. Save.

Lemma SSR_plus_zero_left2 : (n:A) n == 0 + n.
Auto. Save.

Lemma SSR_mult_one_left2 : (n:A) n == 1*n.
Auto. Save.

Lemma SSR_mult_zero_left2 : (n:A) 0 == 0*n.
Auto. Save.

Lemma SSR_distr_left2 : (n,m,p:A) n*p + m*p  == (n + m)*p.
Auto. Save.

Lemma SSR_plus_permute : (n,m,p:A) n+(m+p) == m+(n+p).
Intros.
Rewrite (plus_assoc n m p).
Rewrite (plus_sym n m).
Rewrite <- (plus_assoc m n p).
Trivial.
Save.

Lemma SSR_mult_permute : (n,m,p:A) n*(m*p) == m*(n*p).
Intros.
Rewrite (mult_assoc n m p).
Rewrite (mult_sym n m).
Rewrite <- (mult_assoc m n p).
Trivial.
Save.

Hints Resolve SSR_plus_permute SSR_mult_permute.

Lemma SSR_distr_right : (n,m,p:A) n*(m+p) == (n*m) + (n*p).
Intros.
Rewrite (mult_sym n (Aplus m p)).
Rewrite (mult_sym n m).
Rewrite (mult_sym n p).
Auto.
Save.

Lemma SSR_distr_right2 : (n,m,p:A) (n*m) + (n*p) == n*(m + p).
Intros.
Apply equiv_sym.
Apply SSR_distr_right.
Save.

Lemma SSR_mult_zero_right : (n:A) n*0 == 0.
Intro; Rewrite (mult_sym n Azero); Auto.
Save.

Lemma SSR_mult_zero_right2 : (n:A) 0 == n*0.
Intro; Rewrite (mult_sym n Azero); Auto.
Save.

Lemma SSR_plus_zero_right :(n:A) n + 0 == n.
Intro; Rewrite (plus_sym n Azero); Auto.
Save.

Lemma SSR_plus_zero_right2 :(n:A) n == n + 0.
Intro; Rewrite (plus_sym n Azero); Auto.
Save.

Lemma SSR_mult_one_right : (n:A) n*1 == n.
Intro; Rewrite (mult_sym n Aone); Auto.
Save.

Lemma SSR_mult_one_right2 : (n:A) n == n*1.
Intro; Rewrite (mult_sym n Aone); Auto.
Save.

Lemma SSR_plus_reg_right : (n,m,p:A) m+n == p+n -> m==p.
Intros n m p; Rewrite (plus_sym m n); Rewrite (plus_sym p n).
Intro; Apply plus_reg_left with n; Trivial.
Save.

End Theory_of_semi_setoid_rings.

Section Theory_of_setoid_rings.

Record Setoid_Ring_Theory : Prop :=
{ STh_plus_sym  : (n,m:A) n + m == m + n;
  STh_plus_assoc : (n,m,p:A) n + (m + p) == (n + m) + p;
  STh_mult_sym : (n,m:A) n*m == m*n;
  STh_mult_assoc : (n,m,p:A) n*(m*p) == (n*m)*p;
  STh_plus_zero_left :(n:A) 0 + n == n;
  STh_mult_one_left : (n:A) 1*n == n;
  STh_opp_def : (n:A)  n + (-n) == 0;
  STh_distr_left : (n,m,p:A) (n + m)*p == n*p + m*p;
  STh_eq_prop : (x,y:A) (Is_true (Aeq x y)) -> x == y
}.

Variable T : Setoid_Ring_Theory.

Local plus_sym  := (STh_plus_sym T).
Local plus_assoc := (STh_plus_assoc T).
Local mult_sym  := (STh_mult_sym T).
Local mult_assoc := (STh_mult_assoc T).
Local plus_zero_left := (STh_plus_zero_left T).
Local mult_one_left := (STh_mult_one_left T). 
Local opp_def := (STh_opp_def T).
Local distr_left := (STh_distr_left T).
Local equiv_refl := (Seq_refl A Aequiv S).
Local equiv_sym := (Seq_sym A Aequiv S).
Local equiv_trans := (Seq_trans A Aequiv S).

Hints Resolve plus_sym plus_assoc mult_sym mult_assoc
  plus_zero_left mult_one_left opp_def distr_left
  equiv_refl equiv_sym.

(* Lemmas whose form is x=y are also provided in form y=x because Auto does
  not symmetry *)

Lemma STh_mult_assoc2 : (n,m,p:A) (n * m) * p == n * (m * p).
Auto. Save.

Lemma STh_plus_assoc2 : (n,m,p:A) (n + m) + p == n + (m + p).
Auto. Save.

Lemma STh_plus_zero_left2 : (n:A) n == 0 + n.
Auto. Save.

Lemma STh_mult_one_left2 : (n:A) n == 1*n.
Auto. Save.

Lemma STh_distr_left2 : (n,m,p:A) n*p + m*p  == (n + m)*p.
Auto. Save.

Lemma STh_opp_def2 : (n:A) 0 == n + (-n).
Auto. Save.

Lemma STh_plus_permute : (n,m,p:A) n + (m + p) == m + (n + p).
Intros.
Rewrite (plus_assoc n m p).
Rewrite (plus_sym n m).
Rewrite <- (plus_assoc m n p).
Trivial.
Save.

Lemma STh_mult_permute : (n,m,p:A) n*(m*p) == m*(n*p).
Intros.
Rewrite (mult_assoc n m p).
Rewrite (mult_sym n m).
Rewrite <- (mult_assoc m n p).
Trivial.
Save.

Hints Resolve STh_plus_permute STh_mult_permute.

Lemma Saux1 : (a:A)  a + a == a -> a == 0.
Intros.
Rewrite <- (plus_zero_left a).
Rewrite (plus_sym Azero a).
Setoid_replace (Aplus a Azero) with (Aplus a (Aplus a (Aopp a))); Auto.
Rewrite (plus_assoc a a (Aopp a)).
Rewrite H.
Apply opp_def.
Save.

Lemma STh_mult_zero_left :(n:A) 0*n == 0.
Intros.
Apply Saux1.
Rewrite <- (distr_left Azero Azero n).
Rewrite (plus_zero_left Azero).
Trivial.
Save.
Hints Resolve STh_mult_zero_left.

Lemma STh_mult_zero_left2 : (n:A) 0 == 0*n.
Auto.
Save.

Lemma Saux2 : (x,y,z:A) x+y==0 -> x+z==0 -> y == z.
Intros.
Rewrite <- (plus_zero_left y).
Rewrite <- H0.
Rewrite <- (plus_assoc x z y).
Rewrite (plus_sym z y).
Rewrite (plus_assoc x y z).
Rewrite H.
Auto.
Save.

Lemma STh_opp_mult_left : (x,y:A) -(x*y) == (-x)*y.
Intros.
Apply Saux2 with (Amult x y); Auto.
Rewrite <- (distr_left x (Aopp x) y).
Rewrite (opp_def x).
Auto.
Save.
Hints Resolve STh_opp_mult_left.

Lemma STh_opp_mult_left2 : (x,y:A) (-x)*y == -(x*y) .
Auto.
Save.

Lemma STh_mult_zero_right : (n:A) n*0 == 0.
Intro; Rewrite (mult_sym n Azero); Auto.
Save.

Lemma STh_mult_zero_right2 : (n:A) 0 == n*0.
Intro; Rewrite (mult_sym n Azero); Auto.
Save.

Lemma STh_plus_zero_right :(n:A) n + 0 == n.
Intro; Rewrite (plus_sym n Azero); Auto.
Save.

Lemma STh_plus_zero_right2 :(n:A) n == n + 0.
Intro; Rewrite (plus_sym n Azero); Auto.
Save.

Lemma STh_mult_one_right : (n:A) n*1 == n.
Intro; Rewrite (mult_sym n Aone); Auto.
Save.

Lemma STh_mult_one_right2  : (n:A) n == n*1.
Intro; Rewrite (mult_sym n Aone); Auto.
Save.

Lemma STh_opp_mult_right : (x,y:A) -(x*y) == x*(-y).
Intros.
Rewrite (mult_sym x y).
Rewrite (mult_sym x (Aopp y)).
Auto.
Save.

Lemma STh_opp_mult_right2 : (x,y:A) x*(-y) == -(x*y).
Intros.
Rewrite (mult_sym x y).
Rewrite (mult_sym x (Aopp y)).
Auto.
Save.

Lemma STh_plus_opp_opp : (x,y:A) (-x) + (-y) == -(x+y).
Intros.
Apply Saux2 with (Aplus x y); Auto.
Rewrite (STh_plus_permute (Aplus x y) (Aopp x) (Aopp y)).
Rewrite <- (plus_assoc x y (Aopp y)).
Rewrite (opp_def y); Rewrite (STh_plus_zero_right x).
Rewrite (STh_opp_def2 x); Trivial.
Save.

Lemma STh_plus_permute_opp: (n,m,p:A) (-m)+(n+p) == n+((-m)+p).
Auto.
Save.

Lemma STh_opp_opp : (n:A) -(-n) == n.
Intro.
Apply Saux2 with (Aopp n); Auto.
Rewrite (plus_sym (Aopp n) n); Auto.
Save.
Hints Resolve STh_opp_opp.

Lemma STh_opp_opp2 : (n:A) n == -(-n).
Auto.
Save.

Lemma STh_mult_opp_opp : (x,y:A) (-x)*(-y) == x*y.
Intros.
Rewrite (STh_opp_mult_left2 x (Aopp y)).
Rewrite (STh_opp_mult_right2 x y).
Trivial.
Save.

Lemma STh_mult_opp_opp2 : (x,y:A) x*y == (-x)*(-y).
Intros.
Apply equiv_sym.
Apply STh_mult_opp_opp.
Save.

Lemma STh_opp_zero : -0 == 0.
Rewrite <- (plus_zero_left (Aopp Azero)).
Trivial.
Save.

Lemma STh_plus_reg_left : (n,m,p:A) n+m == n+p -> m==p.
Intros.
Rewrite <- (plus_zero_left m).
Rewrite <- (plus_zero_left p).
Rewrite <- (opp_def n).
Rewrite (plus_sym n (Aopp n)).
Rewrite <- (plus_assoc (Aopp n) n m).
Rewrite <- (plus_assoc (Aopp n) n p).
Auto.
Save.

Lemma STh_plus_reg_right : (n,m,p:A) m+n == p+n -> m==p.
Intros.
Apply STh_plus_reg_left with n.
Rewrite (plus_sym n m); Rewrite (plus_sym n p);
Assumption.
Save.

Lemma STh_distr_right : (n,m,p:A) n*(m+p) == (n*m)+(n*p).
Intros.
Rewrite (mult_sym n (Aplus m p)).
Rewrite (mult_sym n m).
Rewrite (mult_sym n p).
Trivial.
Save.

Lemma STh_distr_right2 : (n,m,p:A) (n*m)+(n*p) == n*(m+p).
Intros.
Apply equiv_sym.
Apply STh_distr_right.
Save.

End Theory_of_setoid_rings.

Hints Resolve STh_mult_zero_left STh_plus_reg_left : core.

Unset Implicit Arguments.

Definition Semi_Setoid_Ring_Theory_of :
  Setoid_Ring_Theory -> Semi_Setoid_Ring_Theory.
Intros until 1; Case H.
Split; Intros; Simpl; EAuto.
Defined.

Coercion Semi_Setoid_Ring_Theory_of :
  Setoid_Ring_Theory >-> Semi_Setoid_Ring_Theory.



Section product_ring.

End product_ring.

Section power_ring.

End power_ring.

End Setoid_rings.
