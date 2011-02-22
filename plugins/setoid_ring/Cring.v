(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* non commutative rings *)

Require Import Setoid.
Require Import BinPos.
Require Import BinNat.
Require Export ZArith.
Require Export Morphisms Setoid Bool.
Require Import Algebra_syntax.
Require Import Ring_theory.

Set Implicit Arguments.

Class Cring (R:Type) := {
 cring0: R; cring1: R; 
 cring_plus: R->R->R; cring_mult: R->R->R;
 cring_sub:  R->R->R; cring_opp: R->R; 
 cring_eq : R -> R -> Prop;
 cring_setoid: Equivalence cring_eq;
 cring_plus_comp: Proper (cring_eq==>cring_eq==>cring_eq) cring_plus;
 cring_mult_comp: Proper (cring_eq==>cring_eq==>cring_eq) cring_mult;
 cring_sub_comp: Proper (cring_eq==>cring_eq==>cring_eq) cring_sub;
 cring_opp_comp: Proper (cring_eq==>cring_eq) cring_opp;

 cring_add_0_l    : forall x, cring_eq (cring_plus cring0 x) x;
 cring_add_comm    : forall x y, cring_eq (cring_plus x y) (cring_plus y x);
 cring_add_assoc  : forall x y z, cring_eq (cring_plus x (cring_plus y z))
                                         (cring_plus (cring_plus x y) z);
 cring_mul_1_l    : forall x, cring_eq (cring_mult cring1 x) x;
 cring_mul_assoc  : forall x y z, cring_eq (cring_mult x (cring_mult y z))
                                         (cring_mult (cring_mult x y) z);
 cring_mul_comm    : forall x y, cring_eq (cring_mult x y) (cring_mult y x);
 cring_distr_l    : forall x y z, cring_eq (cring_mult (cring_plus x y) z)
                                   (cring_plus (cring_mult x z) (cring_mult y z));
 cring_sub_def    : forall x y, cring_eq (cring_sub x y) (cring_plus x (cring_opp y));
 cring_opp_def    : forall x, cring_eq (cring_plus x (cring_opp x)) cring0
}.

(* Syntax *)

Instance zero_cring `{R:Type}`{Rr:Cring R} : Zero R := {zero := cring0}.
Instance one_cring`{R:Type}`{Rr:Cring R} : One R := {one := cring1}.
Instance addition_cring`{R:Type}`{Rr:Cring R} : Addition R :=
  {addition x y := cring_plus x y}.
Instance multiplication_cring`{R:Type}`{Rr:Cring R} : Multiplication:= 
  {multiplication x y := cring_mult x y}.
Instance subtraction_cring`{R:Type}`{Rr:Cring R} : Subtraction R :=
  {subtraction x y := cring_sub x y}.
Instance opposite_cring`{R:Type}`{Rr:Cring R} : Opposite R := 
  {opposite x := cring_opp x}.
Instance equality_cring `{R:Type}`{Rr:Cring R} : Equality :=
  {equality x y := cring_eq x y}.
Definition ZN(x:Z):=
  match x with
    Z0 => N0
    |Zpos p | Zneg p => Npos p
end.
Instance power_cring {R:Type}{Rr:Cring R} : Power:=
  {power x y := @Ring_theory.pow_N _ cring1 cring_mult x (ZN y)}.

Existing Instance cring_setoid.
Existing Instance cring_plus_comp.
Existing Instance cring_mult_comp.
Existing Instance cring_sub_comp.
Existing Instance cring_opp_comp.
(** Interpretation morphisms definition*)

Class Cring_morphism (C R:Type)`{Cr:Cring C} `{Rr:Cring R}:= {
    cring_morphism_fun: C -> R;
    cring_morphism0    : cring_morphism_fun 0 == 0;
    cring_morphism1    : cring_morphism_fun 1 == 1;
    cring_morphism_add : forall x y, cring_morphism_fun (x + y)
                     == cring_morphism_fun x + cring_morphism_fun y;
    cring_morphism_sub : forall x y, cring_morphism_fun (x - y)
                     == cring_morphism_fun x - cring_morphism_fun y;
    cring_morphism_mul : forall x y, cring_morphism_fun (x * y)
                     == cring_morphism_fun x * cring_morphism_fun y;
    cring_morphism_opp : forall x, cring_morphism_fun (-x)
                          == -(cring_morphism_fun x);
    cring_morphism_eq  : forall x y, x == y
       -> cring_morphism_fun x == cring_morphism_fun y}.

Instance bracket_cring {C R:Type}`{Cr:Cring C} `{Rr:Cring R}
   `{phi:@Cring_morphism C R Cr Rr}
  : Bracket C R  :=
  {bracket x := cring_morphism_fun x}.

(* Tactics for crings *)
Axiom eta: forall (A B:Type) (f:A->B), (fun x:A => f x) = f.
Axiom eta2: forall (A B C:Type) (f:A->B->C), (fun (x:A)(y:B) => f x y) = f.

Ltac etarefl := try apply eta; try apply eta2; try reflexivity.

Lemma cring_syntax1:forall (A:Type)(Ar:Cring A), (@cring_eq _ Ar) = equality.
intros. symmetry. simpl; etarefl. Qed.
Lemma cring_syntax2:forall (A:Type)(Ar:Cring A), (@cring_plus _ Ar) = addition.
intros. symmetry. simpl; etarefl. Qed.
Lemma cring_syntax3:forall (A:Type)(Ar:Cring A), (@cring_mult _ Ar) = multiplication.
intros. symmetry. simpl; etarefl. Qed.
Lemma cring_syntax4:forall (A:Type)(Ar:Cring A), (@cring_sub _ Ar) = subtraction.
intros. symmetry. simpl; etarefl. Qed.
Lemma cring_syntax5:forall (A:Type)(Ar:Cring A), (@cring_opp _ Ar) = opposite.
intros. symmetry. simpl; etarefl. Qed.
Lemma cring_syntax6:forall (A:Type)(Ar:Cring A), (@cring0 _ Ar) = zero.
intros. symmetry. simpl; etarefl. Qed.
Lemma cring_syntax7:forall (A:Type)(Ar:Cring A), (@cring1 _ Ar) = one.
intros. symmetry. simpl; etarefl. Qed.
Lemma cring_syntax8:forall (A:Type)(Ar:Cring A)(B:Type)(Br:Cring B)
  (pM:@Cring_morphism A B Ar Br), (@cring_morphism_fun _ _ _ _ pM) = bracket.
intros. symmetry. simpl; etarefl. Qed.

Ltac set_cring_notations :=
  repeat (rewrite cring_syntax1);
  repeat (rewrite cring_syntax2);
  repeat (rewrite cring_syntax3);
  repeat (rewrite cring_syntax4);
  repeat (rewrite cring_syntax5);
  repeat (rewrite cring_syntax6);
  repeat (rewrite cring_syntax7);
  repeat (rewrite cring_syntax8).

Ltac unset_cring_notations :=
  unfold equality, equality_cring, addition, addition_cring,
     multiplication, multiplication_cring, subtraction, subtraction_cring,
     opposite, opposite_cring, one, one_cring, zero, zero_cring,
     bracket, bracket_cring, power, power_cring.

Ltac cring_simpl := simpl; set_cring_notations.

Ltac cring_rewrite H:=
  generalize H;
  let h := fresh "H" in
  unset_cring_notations; intro h;
  rewrite h; clear h;
  set_cring_notations.

Ltac cring_rewrite_rev H:=
  generalize H;
  let h := fresh "H" in
  unset_cring_notations; intro h;
  rewrite <- h; clear h;
  set_cring_notations.

Ltac rrefl := unset_cring_notations; reflexivity.

(* Useful properties *)

Section Cring.

Variable R: Type.
Variable Rr: Cring R.

(* Powers *)

 Fixpoint pow_pos (x:R) (i:positive) {struct i}: R :=
  match i with
  | xH => x
  | xO i => let p := pow_pos x i in p * p
  | xI i => let p := pow_pos x i in x * (p * p)
  end.
Add Setoid R cring_eq cring_setoid as R_set_Power.
 Add Morphism cring_mult : rmul_ext_Power. exact cring_mult_comp. Qed.

 Lemma pow_pos_comm : forall x j,  x * pow_pos x j == pow_pos x j * x.
induction j; cring_simpl. 
cring_rewrite_rev cring_mul_assoc. cring_rewrite_rev cring_mul_assoc. 
cring_rewrite_rev IHj. cring_rewrite (cring_mul_assoc (pow_pos x j) x (pow_pos x j)).
cring_rewrite_rev IHj. cring_rewrite_rev cring_mul_assoc. rrefl.
cring_rewrite_rev cring_mul_assoc. cring_rewrite_rev IHj.
cring_rewrite cring_mul_assoc. cring_rewrite IHj.
cring_rewrite_rev cring_mul_assoc. cring_rewrite IHj. rrefl. rrefl.
Qed.

 Lemma pow_pos_Psucc : forall x j, pow_pos x (Psucc j) == x * pow_pos x j.
 Proof.
  induction j; cring_simpl. 
  cring_rewrite IHj. 
cring_rewrite_rev (cring_mul_assoc x (pow_pos x j) (x * pow_pos x j)).
cring_rewrite (cring_mul_assoc (pow_pos x j) x  (pow_pos x j)).
  cring_rewrite_rev pow_pos_comm. unset_cring_notations.
rewrite <- cring_mul_assoc. reflexivity.
rrefl. rrefl.
Qed.

 Lemma pow_pos_Pplus : forall x i j, pow_pos x (i + j) == pow_pos x i * pow_pos x j.
 Proof.
  intro x;induction i;intros.
  rewrite xI_succ_xO;rewrite Pplus_one_succ_r.
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat cring_rewrite IHi.
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;
  cring_rewrite pow_pos_Psucc.
  cring_simpl;repeat cring_rewrite cring_mul_assoc. rrefl.
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat cring_rewrite IHi. cring_rewrite cring_mul_assoc. rrefl.
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;cring_rewrite pow_pos_Psucc.
   simpl. reflexivity. 
 Qed.

 Definition pow_N (x:R) (p:N) :=
  match p with
  | N0 => 1
  | Npos p => pow_pos x p
  end.

 Definition id_phi_N (x:N) : N := x.

 Lemma pow_N_pow_N : forall x n, pow_N x (id_phi_N n) == pow_N x n.
 Proof.
  intros; rrefl.
 Qed.

End Cring.




Section Cring2.
Variable R: Type.
Variable Rr: Cring R.
 (** Identity is a morphism *)
 Definition IDphi (x:R) := x.
 Lemma IDmorph : @Cring_morphism R R Rr Rr.
 Proof.
  apply (Build_Cring_morphism Rr Rr IDphi);intros;unfold IDphi; try rrefl. trivial.
 Qed.

Ltac cring_replace a b :=
  unset_cring_notations; setoid_replace a with b; set_cring_notations.

 (** crings are almost crings*)
 Lemma cring_mul_0_l : forall x, 0 * x == 0.
 Proof.
  intro x. cring_replace (0*x) ((0+1)*x + -x). 
  cring_rewrite cring_add_0_l. cring_rewrite cring_mul_1_l .
  cring_rewrite cring_opp_def ;rrefl.
  cring_rewrite cring_distr_l ;cring_rewrite cring_mul_1_l .
  cring_rewrite_rev cring_add_assoc ; cring_rewrite cring_opp_def .
  cring_rewrite cring_add_comm ; cring_rewrite cring_add_0_l ;rrefl.
 Qed.

Lemma cring_mul_1_r: forall x, x * 1 == x.
intro x. cring_rewrite (cring_mul_comm x 1). cring_rewrite cring_mul_1_l.
rrefl. Qed.

Lemma cring_distr_r: forall x y z,
  x*(y+z) == x*y + x*z.
intros. cring_rewrite (cring_mul_comm x (y+z)).
cring_rewrite cring_distr_l. cring_rewrite (cring_mul_comm x y).
 cring_rewrite (cring_mul_comm x z). rrefl. Qed.

 Lemma cring_mul_0_r : forall x, x * 0 == 0.
 Proof.
  intro x; cring_replace (x*0)  (x*(0+1) + -x).
  cring_rewrite cring_add_0_l ;  cring_rewrite cring_mul_1_r .
  cring_rewrite cring_opp_def ;rrefl.
  cring_rewrite cring_distr_r . cring_rewrite cring_mul_1_r .
  cring_rewrite_rev cring_add_assoc ; cring_rewrite cring_opp_def .
  cring_rewrite cring_add_comm ; cring_rewrite cring_add_0_l ;rrefl.
 Qed.

 Lemma cring_opp_mul_l : forall x y, -(x * y) == -x * y.
 Proof.
  intros x y;cring_rewrite_rev (cring_add_0_l (- x * y)).
  cring_rewrite cring_add_comm .
  cring_rewrite_rev (cring_opp_def (x*y)).
  cring_rewrite cring_add_assoc .
  cring_rewrite_rev cring_distr_l.
  cring_rewrite (cring_add_comm (-x));cring_rewrite cring_opp_def .
  cring_rewrite cring_mul_0_l;cring_rewrite cring_add_0_l ;rrefl.
 Qed.

Lemma cring_opp_mul_r : forall x y, -(x * y) == x * -y.
 Proof.
  intros x y;cring_rewrite_rev (cring_add_0_l (x * - y)).
  cring_rewrite cring_add_comm .
  cring_rewrite_rev (cring_opp_def (x*y)).
  cring_rewrite cring_add_assoc .
  cring_rewrite_rev cring_distr_r .
  cring_rewrite (cring_add_comm (-y));cring_rewrite cring_opp_def .
  cring_rewrite cring_mul_0_r;cring_rewrite cring_add_0_l ;rrefl.
 Qed.

 Lemma cring_opp_add : forall x y, -(x + y) == -x + -y.
 Proof.
  intros x y;cring_rewrite_rev (cring_add_0_l  (-(x+y))).
  cring_rewrite_rev (cring_opp_def  x).
  cring_rewrite_rev (cring_add_0_l  (x + - x + - (x + y))).
  cring_rewrite_rev (cring_opp_def  y).
  cring_rewrite (cring_add_comm  x).
  cring_rewrite (cring_add_comm  y).
  cring_rewrite_rev (cring_add_assoc  (-y)).
  cring_rewrite_rev (cring_add_assoc  (- x)).
  cring_rewrite (cring_add_assoc   y).
  cring_rewrite (cring_add_comm  y).
  cring_rewrite_rev (cring_add_assoc   (- x)).
  cring_rewrite (cring_add_assoc  y).
  cring_rewrite (cring_add_comm  y);cring_rewrite cring_opp_def .
  cring_rewrite (cring_add_comm  (-x) 0);cring_rewrite cring_add_0_l .
  cring_rewrite cring_add_comm; rrefl.
 Qed.

 Lemma cring_opp_opp : forall x, - -x == x.
 Proof.
  intros x; cring_rewrite_rev (cring_add_0_l (- -x)).
  cring_rewrite_rev (cring_opp_def x).
  cring_rewrite_rev cring_add_assoc ; cring_rewrite cring_opp_def .
  cring_rewrite (cring_add_comm  x); cring_rewrite cring_add_0_l . rrefl.
 Qed.

 Lemma cring_sub_ext :
      forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> x1 - y1 == x2 - y2.
 Proof.
  intros.
  cring_replace (x1 - y1)  (x1 + -y1).
  cring_replace (x2 - y2)  (x2 + -y2).
  cring_rewrite H;cring_rewrite H0;rrefl.
  cring_rewrite cring_sub_def. rrefl.
  cring_rewrite cring_sub_def. rrefl.
 Qed.

 Ltac mcring_rewrite :=
   repeat first
     [ cring_rewrite cring_add_0_l
     | cring_rewrite_rev (cring_add_comm 0)
     | cring_rewrite cring_mul_1_l
     | cring_rewrite cring_mul_0_l
     | cring_rewrite cring_distr_l
     | rrefl
     ].

 Lemma cring_add_0_r : forall x, (x + 0) == x.
 Proof. intros; mcring_rewrite. Qed.

 
 Lemma cring_add_assoc1 : forall x y z, (x + y) + z == (y + z) + x.
 Proof.
  intros;cring_rewrite_rev (cring_add_assoc x).
  cring_rewrite (cring_add_comm x);rrefl.
 Qed.

 Lemma cring_add_assoc2 : forall x y z, (y + x) + z == (y + z) + x.
 Proof.
  intros; repeat cring_rewrite_rev cring_add_assoc.
   cring_rewrite (cring_add_comm x); rrefl.
 Qed.

 Lemma cring_opp_zero : -0 == 0.
 Proof.
  cring_rewrite_rev (cring_mul_0_r 0). cring_rewrite cring_opp_mul_l.
  repeat cring_rewrite cring_mul_0_r. rrefl.
 Qed.

End Cring2.

(** Some simplification tactics*)
Ltac gen_reflexivity := rrefl.
 
Ltac gen_cring_rewrite :=
  repeat first
     [ rrefl
     | progress cring_rewrite cring_opp_zero
     | cring_rewrite cring_add_0_l
     | cring_rewrite cring_add_0_r
     | cring_rewrite cring_mul_1_l 
     | cring_rewrite cring_mul_1_r
     | cring_rewrite cring_mul_0_l 
     | cring_rewrite cring_mul_0_r 
     | cring_rewrite cring_distr_l 
     | cring_rewrite cring_distr_r 
     | cring_rewrite cring_add_assoc 
     | cring_rewrite cring_mul_assoc
     | progress cring_rewrite cring_opp_add 
     | progress cring_rewrite cring_sub_def 
     | progress cring_rewrite_rev cring_opp_mul_l 
     | progress cring_rewrite_rev cring_opp_mul_r ].

Ltac gen_add_push x :=
set_cring_notations;
repeat (match goal with
  | |- context [(?y + x) + ?z] =>
     progress cring_rewrite (@cring_add_assoc2 _ _ x y z)
  | |- context [(x + ?y) + ?z] =>
     progress cring_rewrite  (@cring_add_assoc1 _ _ x y z)
  end).
