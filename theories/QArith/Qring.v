(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Ring.
Require Export Setoid_ring.
Require Export QArith_base.

(** * A ring tactic for rational numbers *)

Definition Qeq_bool (x y : Q) :=
  if Qeq_dec x y then true else false.

Lemma Qeq_bool_correct : forall x y : Q, Qeq_bool x y = true -> x==y.
intros x y; unfold Qeq_bool in |- *; case (Qeq_dec x y); simpl in |- *; auto.
intros _ H; inversion H.
Qed.

Definition Qsrt : Setoid_Ring_Theory Qeq Qplus Qmult 1 0 Qopp Qeq_bool.
Proof.
constructor.
exact Qplus_comm.
exact Qplus_assoc.
exact Qmult_comm.
exact Qmult_assoc.
exact Qplus_0_l.
exact Qmult_1_l.
exact Qplus_opp_r.
exact Qmult_plus_distr_l.
unfold Is_true; intros x y; generalize (Qeq_bool_correct x y);
 case (Qeq_bool x y); auto.
Qed.

Add Setoid Ring Q Qeq Q_Setoid Qplus Qmult 1 0 Qopp Qeq_bool
 Qplus_comp Qmult_comp Qopp_comp Qsrt
 [ Qmake (*inject_Z*)  Zpos 0%Z Zneg xI xO 1%positive ].

(** Exemple of use: *)

Section Examples. 

Let ex1 : forall x y z : Q, (x+y)*z ==  (x*z)+(y*z).
intros.
ring.
Qed.

Let ex2 : forall x y : Q, x+y == y+x.
intros. 
ring.
Qed.

Let ex3 : forall x y z : Q, (x+y)+z == x+(y+z).
intros.
ring.
Qed.

Let ex4 : (inject_Z 1)+(inject_Z 1)==(inject_Z 2).
ring.
Qed.

Let ex5 : 1+1 == 2#1.
ring.
Qed.

Let ex6 : (1#1)+(1#1) == 2#1.
ring.
Qed.

Let ex7 : forall x : Q, x-x== 0#1.
intro.
ring.
Qed.

End Examples.

Lemma Qopp_plus : forall a b,  -(a+b) == -a + -b.
Proof.
intros; ring.
Qed.

Lemma Qopp_opp : forall q, - -q==q.
Proof.
intros; ring.
Qed.

