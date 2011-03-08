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
Require Export Morphisms Setoid Bool.
Require Export Algebra_syntax.

Set Implicit Arguments.

Class Ring (R:Type) := {
 ring0: R; ring1: R; 
 ring_plus: R->R->R; ring_mult: R->R->R;
 ring_sub:  R->R->R; ring_opp: R->R; 
 ring_eq : R -> R -> Prop;
 ring_setoid: Equivalence ring_eq;
 ring_plus_comp: Proper (ring_eq==>ring_eq==>ring_eq) ring_plus;
 ring_mult_comp: Proper (ring_eq==>ring_eq==>ring_eq) ring_mult;
 ring_sub_comp: Proper (ring_eq==>ring_eq==>ring_eq) ring_sub;
 ring_opp_comp: Proper (ring_eq==>ring_eq) ring_opp;

 ring_add_0_l    : forall x, ring_eq (ring_plus ring0 x) x;
 ring_add_comm    : forall x y, ring_eq (ring_plus x y) (ring_plus y x);
 ring_add_assoc  : forall x y z, ring_eq (ring_plus x (ring_plus y z))
                                         (ring_plus (ring_plus x y) z);
 ring_mul_1_l    : forall x, ring_eq (ring_mult ring1 x) x;
 ring_mul_1_r    : forall x, ring_eq (ring_mult x ring1) x;
 ring_mul_assoc  : forall x y z, ring_eq (ring_mult x (ring_mult y z))
                                         (ring_mult (ring_mult x y) z);
 ring_distr_l    : forall x y z, ring_eq (ring_mult (ring_plus x y) z)
                                   (ring_plus (ring_mult x z) (ring_mult y z));
 ring_distr_r    : forall x y z, ring_eq (ring_mult z (ring_plus x y))
                                  (ring_plus (ring_mult z x) (ring_mult z y));
 ring_sub_def    : forall x y, ring_eq (ring_sub x y) (ring_plus x (ring_opp y));
 ring_opp_def    : forall x, ring_eq (ring_plus x (ring_opp x)) ring0
}.


Instance zero_ring (R:Type)(Rr:Ring R) : Zero R := {zero := ring0}.
Instance one_ring(R:Type)(Rr:Ring R) : One R := {one := ring1}.
Instance addition_ring(R:Type)(Rr:Ring R) : Addition R :=
  {addition x y := ring_plus x y}.
Instance multiplication_ring(R:Type)(Rr:Ring R) : Multiplication:= 
  {multiplication x y := ring_mult x y}.
Instance subtraction_ring(R:Type)(Rr:Ring R) : Subtraction R :=
  {subtraction x y := ring_sub x y}.
Instance opposite_ring(R:Type)(Rr:Ring R) : Opposite R := 
  {opposite x := ring_opp x}.
Instance equality_ring(R:Type)(Rr:Ring R) : Equality :=
  {equality x y := ring_eq x y}.

Existing Instance ring_setoid.
Existing Instance ring_plus_comp.
Existing Instance ring_mult_comp.
Existing Instance ring_sub_comp.
Existing Instance ring_opp_comp.
(** Interpretation morphisms definition*)

Class Ring_morphism (C R:Type)`{Cr:Ring C} `{Rr:Ring R}:= {
    ring_morphism_fun: C -> R;
    ring_morphism0    : ring_morphism_fun 0 == 0;
    ring_morphism1    : ring_morphism_fun 1 == 1;
    ring_morphism_add : forall x y, ring_morphism_fun (x + y)
                     == ring_morphism_fun x + ring_morphism_fun y;
    ring_morphism_sub : forall x y, ring_morphism_fun (x - y)
                     == ring_morphism_fun x - ring_morphism_fun y;
    ring_morphism_mul : forall x y, ring_morphism_fun (x * y)
                     == ring_morphism_fun x * ring_morphism_fun y;
    ring_morphism_opp : forall x, ring_morphism_fun (-x)
                          == -(ring_morphism_fun x);
    ring_morphism_eq  : forall x y, x == y
       -> ring_morphism_fun x == ring_morphism_fun y}.

Instance bracket_ring (C R:Type)`{Cr:Ring C} `{Rr:Ring R}
   `{phi:@Ring_morphism C R Cr Rr}
  : Bracket C R  :=
  {bracket x := ring_morphism_fun x}.

(* Tactics for rings *)

Lemma ring_syntax1:forall (A:Type)(Ar:Ring A), (@ring_eq _ Ar) = equality.
intros. symmetry. simpl; reflexivity. Qed.
Lemma ring_syntax2:forall (A:Type)(Ar:Ring A), (@ring_plus _ Ar) = addition.
intros. symmetry. simpl; reflexivity. Qed.
Lemma ring_syntax3:forall (A:Type)(Ar:Ring A), (@ring_mult _ Ar) = multiplication.
intros. symmetry. simpl; reflexivity. Qed.
Lemma ring_syntax4:forall (A:Type)(Ar:Ring A), (@ring_sub _ Ar) = subtraction.
intros. symmetry. simpl; reflexivity. Qed.
Lemma ring_syntax5:forall (A:Type)(Ar:Ring A), (@ring_opp _ Ar) = opposite.
intros. symmetry. simpl; reflexivity. Qed.
Lemma ring_syntax6:forall (A:Type)(Ar:Ring A), (@ring0 _ Ar) = zero.
intros. symmetry. simpl; reflexivity. Qed.
Lemma ring_syntax7:forall (A:Type)(Ar:Ring A), (@ring1 _ Ar) = one.
intros. symmetry. simpl; reflexivity. Qed.
Lemma ring_syntax8:forall (A:Type)(Ar:Ring A)(B:Type)(Br:Ring B)
  (pM:@Ring_morphism A B Ar Br), (@ring_morphism_fun _ _ _ _ pM) = bracket.
intros. symmetry. simpl; reflexivity. Qed.

Ltac set_ring_notations :=
  repeat (rewrite ring_syntax1);
  repeat (rewrite ring_syntax2);
  repeat (rewrite ring_syntax3);
  repeat (rewrite ring_syntax4);
  repeat (rewrite ring_syntax5);
  repeat (rewrite ring_syntax6);
  repeat (rewrite ring_syntax7);
  repeat (rewrite ring_syntax8).

Ltac unset_ring_notations :=
  unfold equality, equality_ring, addition, addition_ring,
     multiplication, multiplication_ring, subtraction, subtraction_ring,
     opposite, opposite_ring, one, one_ring, zero, zero_ring,
     bracket, bracket_ring.

Ltac ring_simpl := simpl; set_ring_notations.

Ltac ring_rewrite H:=
  generalize H;
  let h := fresh "H" in
  unset_ring_notations; intro h;
  rewrite h; clear h;
  set_ring_notations.

Ltac ring_rewrite_rev H:=
  generalize H;
  let h := fresh "H" in
  unset_ring_notations; intro h;
  rewrite <- h; clear h;
  set_ring_notations.

Ltac rrefl := unset_ring_notations; reflexivity.

Section Ring.

Variable R: Type.
Variable Rr: Ring R.

(* Powers *)

 Fixpoint pow_pos (x:R) (i:positive) {struct i}: R :=
  match i with
  | xH => x
  | xO i => let p := pow_pos x i in p * p
  | xI i => let p := pow_pos x i in x * (p * p)
  end.
Add Setoid R ring_eq ring_setoid as R_set_Power.
 Add Morphism ring_mult : rmul_ext_Power. exact ring_mult_comp. Qed.

 Lemma pow_pos_comm : forall x j,  x * pow_pos x j == pow_pos x j * x.
induction j; ring_simpl. 
ring_rewrite_rev ring_mul_assoc. ring_rewrite_rev ring_mul_assoc. 
ring_rewrite_rev IHj. ring_rewrite (ring_mul_assoc (pow_pos x j) x (pow_pos x j)).
ring_rewrite_rev IHj. ring_rewrite_rev ring_mul_assoc. rrefl.
ring_rewrite_rev ring_mul_assoc. ring_rewrite_rev IHj.
ring_rewrite ring_mul_assoc. ring_rewrite IHj.
ring_rewrite_rev ring_mul_assoc. ring_rewrite IHj. rrefl. rrefl.
Qed.

 Lemma pow_pos_Psucc : forall x j, pow_pos x (Psucc j) == x * pow_pos x j.
 Proof.
  induction j; ring_simpl. 
  ring_rewrite IHj. 
ring_rewrite_rev (ring_mul_assoc x (pow_pos x j) (x * pow_pos x j)).
ring_rewrite (ring_mul_assoc (pow_pos x j) x  (pow_pos x j)).
  ring_rewrite_rev pow_pos_comm. unset_ring_notations.
rewrite <- ring_mul_assoc. reflexivity.
rrefl. rrefl.
Qed.

 Lemma pow_pos_Pplus : forall x i j, pow_pos x (i + j) == pow_pos x i * pow_pos x j.
 Proof.
  intro x;induction i;intros.
  rewrite xI_succ_xO;rewrite Pplus_one_succ_r.
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat ring_rewrite IHi.
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;
  ring_rewrite pow_pos_Psucc.
  ring_simpl;repeat ring_rewrite ring_mul_assoc. rrefl.
  rewrite <- Pplus_diag;repeat rewrite <- Pplus_assoc.
  repeat ring_rewrite IHi. ring_rewrite ring_mul_assoc. rrefl.
  rewrite Pplus_comm;rewrite <- Pplus_one_succ_r;ring_rewrite pow_pos_Psucc.
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

End Ring.




Section Ring2.
Variable R: Type.
Variable Rr: Ring R.
 (** Identity is a morphism *)
 Definition IDphi (x:R) := x.
 Lemma IDmorph : @Ring_morphism R R Rr Rr.
 Proof.
  apply (Build_Ring_morphism Rr Rr IDphi);intros;unfold IDphi; try rrefl. trivial.
 Qed.

Ltac ring_replace a b :=
  unset_ring_notations; setoid_replace a with b; set_ring_notations.

 (** rings are almost rings*)
 Lemma ring_mul_0_l : forall x, 0 * x == 0.
 Proof.
  intro x. ring_replace (0*x) ((0+1)*x + -x). 
  ring_rewrite ring_add_0_l. ring_rewrite ring_mul_1_l .
  ring_rewrite ring_opp_def ;rrefl.
  ring_rewrite ring_distr_l ;ring_rewrite ring_mul_1_l .
  ring_rewrite_rev ring_add_assoc ; ring_rewrite ring_opp_def .
  ring_rewrite ring_add_comm ; ring_rewrite ring_add_0_l ;rrefl.
 Qed.

 Lemma ring_mul_0_r : forall x, x * 0 == 0.
 Proof.
  intro x; ring_replace (x*0)  (x*(0+1) + -x).
  ring_rewrite ring_add_0_l ; ring_rewrite ring_mul_1_r .
  ring_rewrite ring_opp_def ;rrefl.

  ring_rewrite ring_distr_r ;ring_rewrite ring_mul_1_r .
  ring_rewrite_rev ring_add_assoc ; ring_rewrite ring_opp_def .
  ring_rewrite ring_add_comm ; ring_rewrite ring_add_0_l ;rrefl.
 Qed.

 Lemma ring_opp_mul_l : forall x y, -(x * y) == -x * y.
 Proof.
  intros x y;ring_rewrite_rev (ring_add_0_l (- x * y)).
  ring_rewrite ring_add_comm .
  ring_rewrite_rev (ring_opp_def (x*y)).
  ring_rewrite ring_add_assoc .
  ring_rewrite_rev ring_distr_l.
  ring_rewrite (ring_add_comm (-x));ring_rewrite ring_opp_def .
  ring_rewrite ring_mul_0_l;ring_rewrite ring_add_0_l ;rrefl.
 Qed.

Lemma ring_opp_mul_r : forall x y, -(x * y) == x * -y.
 Proof.
  intros x y;ring_rewrite_rev (ring_add_0_l (x * - y)).
  ring_rewrite ring_add_comm .
  ring_rewrite_rev (ring_opp_def (x*y)).
  ring_rewrite ring_add_assoc .
  ring_rewrite_rev ring_distr_r .
  ring_rewrite (ring_add_comm (-y));ring_rewrite ring_opp_def .
  ring_rewrite ring_mul_0_r;ring_rewrite ring_add_0_l ;rrefl.
 Qed.

 Lemma ring_opp_add : forall x y, -(x + y) == -x + -y.
 Proof.
  intros x y;ring_rewrite_rev (ring_add_0_l  (-(x+y))).
  ring_rewrite_rev (ring_opp_def  x).
  ring_rewrite_rev (ring_add_0_l  (x + - x + - (x + y))).
  ring_rewrite_rev (ring_opp_def  y).
  ring_rewrite (ring_add_comm  x).
  ring_rewrite (ring_add_comm  y).
  ring_rewrite_rev (ring_add_assoc  (-y)).
  ring_rewrite_rev (ring_add_assoc  (- x)).
  ring_rewrite (ring_add_assoc   y).
  ring_rewrite (ring_add_comm  y).
  ring_rewrite_rev (ring_add_assoc   (- x)).
  ring_rewrite (ring_add_assoc  y).
  ring_rewrite (ring_add_comm  y);ring_rewrite ring_opp_def .
  ring_rewrite (ring_add_comm  (-x) 0);ring_rewrite ring_add_0_l .
  ring_rewrite ring_add_comm; rrefl.
 Qed.

 Lemma ring_opp_opp : forall x, - -x == x.
 Proof.
  intros x; ring_rewrite_rev (ring_add_0_l (- -x)).
  ring_rewrite_rev (ring_opp_def x).
  ring_rewrite_rev ring_add_assoc ; ring_rewrite ring_opp_def .
  ring_rewrite (ring_add_comm  x); ring_rewrite ring_add_0_l . rrefl.
 Qed.

 Lemma ring_sub_ext :
      forall x1 x2, x1 == x2 -> forall y1 y2, y1 == y2 -> x1 - y1 == x2 - y2.
 Proof.
  intros.
  ring_replace (x1 - y1)  (x1 + -y1).
  ring_replace (x2 - y2)  (x2 + -y2).
  ring_rewrite H;ring_rewrite H0;rrefl.
  ring_rewrite ring_sub_def. rrefl.
  ring_rewrite ring_sub_def. rrefl.
 Qed.

 Ltac mring_rewrite :=
   repeat first
     [ ring_rewrite ring_add_0_l
     | ring_rewrite_rev (ring_add_comm 0)
     | ring_rewrite ring_mul_1_l
     | ring_rewrite ring_mul_0_l
     | ring_rewrite ring_distr_l
     | rrefl
     ].

 Lemma ring_add_0_r : forall x, (x + 0) == x.
 Proof. intros; mring_rewrite. Qed.

 
 Lemma ring_add_assoc1 : forall x y z, (x + y) + z == (y + z) + x.
 Proof.
  intros;ring_rewrite_rev (ring_add_assoc x).
  ring_rewrite (ring_add_comm x);rrefl.
 Qed.

 Lemma ring_add_assoc2 : forall x y z, (y + x) + z == (y + z) + x.
 Proof.
  intros; repeat ring_rewrite_rev ring_add_assoc.
   ring_rewrite (ring_add_comm x); rrefl.
 Qed.

 Lemma ring_opp_zero : -0 == 0.
 Proof.
  ring_rewrite_rev (ring_mul_0_r 0). ring_rewrite ring_opp_mul_l.
  repeat ring_rewrite ring_mul_0_r. rrefl.
 Qed.

End Ring2.

(** Some simplification tactics*)
Ltac gen_reflexivity := rrefl.
 
Ltac gen_ring_rewrite :=
  repeat first
     [ rrefl
     | progress ring_rewrite ring_opp_zero
     | ring_rewrite ring_add_0_l
     | ring_rewrite ring_add_0_r
     | ring_rewrite ring_mul_1_l 
     | ring_rewrite ring_mul_1_r
     | ring_rewrite ring_mul_0_l 
     | ring_rewrite ring_mul_0_r 
     | ring_rewrite ring_distr_l 
     | ring_rewrite ring_distr_r 
     | ring_rewrite ring_add_assoc 
     | ring_rewrite ring_mul_assoc
     | progress ring_rewrite ring_opp_add 
     | progress ring_rewrite ring_sub_def 
     | progress ring_rewrite_rev ring_opp_mul_l 
     | progress ring_rewrite_rev ring_opp_mul_r ].

Ltac gen_add_push x :=
set_ring_notations;
repeat (match goal with
  | |- context [(?y + x) + ?z] =>
     progress ring_rewrite (@ring_add_assoc2 _ _ x y z)
  | |- context [(x + ?y) + ?z] =>
     progress ring_rewrite  (@ring_add_assoc1 _ _ x y z)
  end).
