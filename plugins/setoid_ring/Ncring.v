(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* non commutative rings *)

Require Import Setoid.
Require Import BinPos.
Require Import BinNat.
Require Export Morphisms Setoid Bool.
Require Export ZArith_base.
Require Export Algebra_syntax.

Set Implicit Arguments.

Class Ring_ops(T:Type)
   {ring0:T}
   {ring1:T}
   {add:T->T->T}
   {mul:T->T->T}
   {sub:T->T->T}
   {opp:T->T}
   {ring_eq:T->T->Prop}.

Instance zero_notation(T:Type)`{Ring_ops T}:Zero T:= ring0. 
Instance one_notation(T:Type)`{Ring_ops T}:One T:= ring1.
Instance add_notation(T:Type)`{Ring_ops T}:Addition T:= add.
Instance mul_notation(T:Type)`{Ring_ops T}:@Multiplication T T:= mul.
Instance sub_notation(T:Type)`{Ring_ops T}:Subtraction T:= sub.
Instance opp_notation(T:Type)`{Ring_ops T}:Opposite T:= opp.
Instance eq_notation(T:Type)`{Ring_ops T}:@Equality T:= ring_eq.

Class Ring `{Ro:Ring_ops}:={
 ring_setoid: Equivalence _==_;
 ring_plus_comp: Proper (_==_ ==> _==_ ==>_==_) _+_;
 ring_mult_comp: Proper (_==_ ==> _==_ ==>_==_) _*_;
 ring_sub_comp: Proper (_==_ ==> _==_ ==>_==_) _-_;
 ring_opp_comp: Proper (_==_==>_==_) -_;
 ring_add_0_l    : forall x, 0 + x == x;
 ring_add_comm   : forall x y, x + y == y + x;
 ring_add_assoc  : forall x y z, x + (y + z) == (x + y) + z;
 ring_mul_1_l    : forall x, 1 * x == x;
 ring_mul_1_r    : forall x, x * 1 == x;
 ring_mul_assoc  : forall x y z, x * (y * z) == (x * y) * z;
 ring_distr_l    : forall x y z, (x + y) * z == x * z + y * z;
 ring_distr_r    : forall x y z, z * ( x + y) == z * x + z * y;
 ring_sub_def    : forall x y, x - y == x + -y;
 ring_opp_def    : forall x, x + -x == 0
}.
(* inutile! je sais plus pourquoi j'ai mis ca...
Instance ring_Ring_ops(R:Type)`{Ring R}
  :@Ring_ops R 0 1 addition multiplication subtraction opposite equality.
*)
Existing Instance ring_setoid.
Existing Instance ring_plus_comp.
Existing Instance ring_mult_comp.
Existing Instance ring_sub_comp.
Existing Instance ring_opp_comp.

Section Ring_power.

Context {R:Type}`{Ring R}.

 Fixpoint pow_pos (x:R) (i:positive) {struct i}: R :=
  match i with
  | xH => x
  | xO i => let p := pow_pos x i in p * p
  | xI i => let p := pow_pos x i in x * (p * p)
  end.

 Definition pow_N (x:R) (p:N) :=
  match p with
  | N0 => 1
  | Npos p => pow_pos x p
  end.

End Ring_power.

Definition ZN(x:Z):=
  match x with
    Z0 => N0
    |Zpos p | Zneg p => Npos p
end.

Instance power_ring {R:Type}`{Ring R} : Power:=
  {power x y := pow_N x (ZN y)}.

(** Interpretation morphisms definition*)

Class Ring_morphism (C R:Type)`{Cr:Ring C} `{Rr:Ring R}`{Rh:Bracket C R}:= {
    ring_morphism0    : [0] == 0;
    ring_morphism1    : [1] == 1;
    ring_morphism_add : forall x y, [x + y] == [x] + [y];
    ring_morphism_sub : forall x y, [x - y] == [x] - [y];
    ring_morphism_mul : forall x y, [x * y] == [x] * [y];
    ring_morphism_opp : forall  x, [-x] == -[x];
    ring_morphism_eq  : forall x y, x == y -> [x] == [y]}.

Section Ring.

Context {R:Type}`{Rr:Ring R}.

(* Powers *)

Lemma pow_pos_comm : forall  x j,  x * pow_pos x j == pow_pos x j * x.
Proof.
induction j; simpl. rewrite <- ring_mul_assoc.
rewrite <- ring_mul_assoc.
rewrite <- IHj. rewrite (ring_mul_assoc (pow_pos x j) x (pow_pos x j)).
rewrite <- IHj. rewrite <- ring_mul_assoc. reflexivity.
rewrite <- ring_mul_assoc. rewrite <- IHj.
rewrite ring_mul_assoc. rewrite IHj.
rewrite <- ring_mul_assoc. rewrite IHj. reflexivity. reflexivity.
Qed.

Lemma pow_pos_succ : forall  x j, pow_pos x (Pos.succ j) == x * pow_pos x j.
Proof.
induction j; simpl.
  rewrite IHj.
rewrite <- (ring_mul_assoc x (pow_pos x j) (x * pow_pos x j)).
rewrite (ring_mul_assoc (pow_pos x j) x  (pow_pos x j)).
  rewrite <- pow_pos_comm.
rewrite <- ring_mul_assoc. reflexivity.
reflexivity. reflexivity.
Qed.

Lemma pow_pos_add : forall  x i j,
  pow_pos x (i + j) == pow_pos x i * pow_pos x j.
Proof.
  intro x;induction i;intros.
  rewrite Pos.xI_succ_xO;rewrite <- Pos.add_1_r.
  rewrite <- Pos.add_diag;repeat rewrite <- Pos.add_assoc.
  repeat rewrite IHi.
  rewrite Pos.add_comm;rewrite Pos.add_1_r;
  rewrite pow_pos_succ.
  simpl;repeat rewrite ring_mul_assoc. reflexivity.
  rewrite <- Pos.add_diag;repeat rewrite <- Pos.add_assoc.
  repeat rewrite IHi. rewrite ring_mul_assoc. reflexivity.
  rewrite Pos.add_comm;rewrite Pos.add_1_r;rewrite pow_pos_succ.
   simpl. reflexivity.
 Qed.

 Definition id_phi_N (x:N) : N := x.

 Lemma pow_N_pow_N : forall  x n, pow_N x (id_phi_N n) == pow_N x n.
 Proof.
  intros; reflexivity.
 Qed.

 (** Identity is a morphism *)
 (*
 Instance IDmorph : Ring_morphism _ _ _  (fun x => x).
 Proof.
  apply (Build_Ring_morphism H6 H6 (fun x => x));intros;
  try reflexivity. trivial.
 Qed.
*)
 (** rings are almost rings*)
 Lemma ring_mul_0_l : forall  x, 0 * x == 0.
 Proof.
  intro x. setoid_replace (0*x) with ((0+1)*x + -x). 
  rewrite ring_add_0_l. rewrite ring_mul_1_l .
  rewrite ring_opp_def . fold zero. reflexivity.
  rewrite ring_distr_l . rewrite ring_mul_1_l .
  rewrite <- ring_add_assoc ; rewrite ring_opp_def .
  rewrite ring_add_comm ; rewrite ring_add_0_l ;reflexivity.
 Qed.

 Lemma ring_mul_0_r : forall  x, x * 0 == 0.
 Proof.
  intro x; setoid_replace (x*0)  with (x*(0+1) + -x).
  rewrite ring_add_0_l ; rewrite ring_mul_1_r .
  rewrite ring_opp_def ; fold zero; reflexivity.

  rewrite ring_distr_r ;rewrite ring_mul_1_r .
  rewrite <- ring_add_assoc ; rewrite ring_opp_def .
  rewrite ring_add_comm ; rewrite ring_add_0_l ;reflexivity.
 Qed.

 Lemma ring_opp_mul_l : forall x y, -(x * y) == -x * y.
 Proof.
  intros x y;rewrite <- (ring_add_0_l (- x * y)).
  rewrite ring_add_comm .
  rewrite <- (ring_opp_def (x*y)).
  rewrite ring_add_assoc .
  rewrite <- ring_distr_l.
  rewrite (ring_add_comm (-x));rewrite ring_opp_def .
  rewrite ring_mul_0_l;rewrite ring_add_0_l ;reflexivity.
 Qed.

Lemma ring_opp_mul_r : forall x y, -(x * y) == x * -y.
 Proof.
  intros x y;rewrite <- (ring_add_0_l (x * - y)).
  rewrite ring_add_comm .
  rewrite <- (ring_opp_def (x*y)).
  rewrite ring_add_assoc .
  rewrite <- ring_distr_r .
  rewrite (ring_add_comm (-y));rewrite ring_opp_def .
  rewrite ring_mul_0_r;rewrite ring_add_0_l ;reflexivity.
 Qed.

 Lemma ring_opp_add : forall x y, -(x + y) == -x + -y.
 Proof.
  intros x y;rewrite <- (ring_add_0_l  (-(x+y))).
  rewrite <- (ring_opp_def  x).
  rewrite <- (ring_add_0_l  (x + - x + - (x + y))).
  rewrite <- (ring_opp_def  y).
  rewrite (ring_add_comm  x).
  rewrite (ring_add_comm  y).
  rewrite <- (ring_add_assoc  (-y)).
  rewrite <- (ring_add_assoc  (- x)).
  rewrite (ring_add_assoc   y).
  rewrite (ring_add_comm  y).
  rewrite <- (ring_add_assoc   (- x)).
  rewrite (ring_add_assoc  y).
  rewrite (ring_add_comm  y);rewrite ring_opp_def .
  rewrite (ring_add_comm  (-x) 0);rewrite ring_add_0_l .
  rewrite ring_add_comm; reflexivity.
 Qed.

 Lemma ring_opp_opp : forall  x, - -x == x.
 Proof.
  intros x; rewrite <- (ring_add_0_l (- -x)).
  rewrite <- (ring_opp_def x).
  rewrite <- ring_add_assoc ; rewrite ring_opp_def .
  rewrite (ring_add_comm  x); rewrite ring_add_0_l . reflexivity.
 Qed.

 Lemma ring_sub_ext :
      forall  x1 x2, x1 == x2 -> forall  y1 y2, y1 == y2 -> x1 - y1 == x2 - y2.
 Proof.
  intros.
  setoid_replace (x1 - y1)  with (x1 + -y1).
  setoid_replace (x2 - y2)  with (x2 + -y2).
  rewrite H;rewrite H0;reflexivity.
  rewrite ring_sub_def. reflexivity.
  rewrite ring_sub_def. reflexivity.
 Qed.

 Ltac mrewrite :=
   repeat first
     [ rewrite ring_add_0_l
     | rewrite <- (ring_add_comm 0)
     | rewrite ring_mul_1_l
     | rewrite ring_mul_0_l
     | rewrite ring_distr_l
     | reflexivity
     ].

 Lemma ring_add_0_r : forall  x, (x + 0) == x.
 Proof. intros; mrewrite. Qed.

 
 Lemma ring_add_assoc1 : forall x y z, (x + y) + z == (y + z) + x.
 Proof.
  intros;rewrite <- (ring_add_assoc x).
  rewrite (ring_add_comm x);reflexivity.
 Qed.

 Lemma ring_add_assoc2 : forall x y z, (y + x) + z == (y + z) + x.
 Proof.
  intros; repeat rewrite <- ring_add_assoc.
   rewrite (ring_add_comm x); reflexivity.
 Qed.

 Lemma ring_opp_zero : -0 == 0.
 Proof.
  rewrite <- (ring_mul_0_r 0). rewrite ring_opp_mul_l.
  repeat rewrite ring_mul_0_r. reflexivity.
 Qed.

End Ring.

(** Some simplification tactics*)
Ltac gen_reflexivity := reflexivity.
 
Ltac gen_rewrite :=
  repeat first
     [ reflexivity
     | progress rewrite ring_opp_zero
     | rewrite ring_add_0_l
     | rewrite ring_add_0_r
     | rewrite ring_mul_1_l 
     | rewrite ring_mul_1_r
     | rewrite ring_mul_0_l 
     | rewrite ring_mul_0_r 
     | rewrite ring_distr_l 
     | rewrite ring_distr_r 
     | rewrite ring_add_assoc 
     | rewrite ring_mul_assoc
     | progress rewrite ring_opp_add 
     | progress rewrite ring_sub_def 
     | progress rewrite <- ring_opp_mul_l 
     | progress rewrite <- ring_opp_mul_r ].

Ltac gen_add_push x :=
repeat (match goal with
  | |- context [(?y + x) + ?z] =>
     progress rewrite (ring_add_assoc2 x y z)
  | |- context [(x + ?y) + ?z] =>
     progress rewrite  (ring_add_assoc1 x y z)
  end).
