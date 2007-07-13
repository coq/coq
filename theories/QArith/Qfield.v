(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: Qring.v 9427 2006-12-11 18:46:35Z bgregoir $ i*)

Require Export Field.
Require Export QArith_base.
Require Import NArithRing.

(** * field and ring tactics for rational numbers *)

Definition Qeq_bool (x y : Q) :=
  if Qeq_dec x y then true else false.

Lemma Qeq_bool_correct : forall x y : Q, Qeq_bool x y = true -> x==y.
Proof.
  intros x y; unfold Qeq_bool in |- *; case (Qeq_dec x y); simpl in |- *; auto.
  intros _ H; inversion H.
Qed.

Lemma Qeq_bool_complete : forall x y : Q, x==y -> Qeq_bool x y = true.
Proof.
  intros x y; unfold Qeq_bool in |- *; case (Qeq_dec x y); simpl in |- *; auto.
Qed.

Definition Qsft : field_theory 0 1 Qplus Qmult Qminus Qopp Qdiv Qinv Qeq.
Proof.
  constructor.
  constructor.
  exact Qplus_0_l.
  exact Qplus_comm.
  exact Qplus_assoc.
  exact Qmult_1_l.
  exact Qmult_comm.
  exact Qmult_assoc.
  exact Qmult_plus_distr_l.
  reflexivity.
  exact Qplus_opp_r.
  discriminate.
  reflexivity.
  intros p Hp.
  rewrite Qmult_comm.
  apply Qmult_inv_r.
  exact Hp.
Qed.

Lemma Qpower_theory : power_theory 1 Qmult Qeq Z_of_N Qpower.
Proof.
constructor.
intros r [|n];
reflexivity.
Qed.

Ltac isQcst t :=
  match t with
  | inject_Z ?z => isZcst z
  | Qmake ?n ?d =>
    match isZcst n with
      true => isPcst d
    | _ => false
    end
  | _ => false
  end.

Ltac Qcst t :=
  match isQcst t with
    true => t
    | _ => NotConstant
  end.

Ltac Qpow_tac t :=
  match t with
  | Z0 => N0
  | Zpos ?n => Ncst (Npos n)
  | Z_of_N ?n => Ncst n
  | NtoZ ?n => Ncst n
  | _ => NotConstant
  end.

Add Field Qfield : Qsft 
 (decidable Qeq_bool_correct, 
  completeness Qeq_bool_complete,
  constants [Qcst], 
  power_tac Qpower_theory [Qpow_tac]).

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

Let ex7 : forall x : Q, x-x== 0.
  intro.
  ring.
Qed.

Let ex8 : forall x : Q, x^1 == x.
  intro.
  ring.
Qed.

Let ex9 : forall x : Q, x^0 == 1.
  intro.
  ring.
Qed.

Let ex10 : forall x y : Q, ~(y==0) -> (x/y)*y == x.
intros.
field.
auto.
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
