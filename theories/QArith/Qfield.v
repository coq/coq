(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Field.
Require Export QArith_base.
Require Import NArithRing.

(** * field and ring tactics for rational numbers *)

Lemma Qsrt : ring_theory 0 1 Qplus Qmult Qminus Qopp Qeq.
Proof.
  constructor.
  - exact Qplus_0_l.
  - exact Qplus_comm.
  - exact Qplus_assoc.
  - exact Qmult_1_l.
  - exact Qmult_comm.
  - exact Qmult_assoc.
  - exact Qmult_plus_distr_l.
  - reflexivity.
  - exact Qplus_opp_r.
Qed.

Lemma Qsft : field_theory 0 1 Qplus Qmult Qminus Qopp Qdiv Qinv Qeq.
Proof.
  constructor.
  - exact Qsrt.
  - discriminate.
  - reflexivity.
  - intros p Hp.
    rewrite Qmult_comm.
    apply Qmult_inv_r.
    exact Hp.
Qed.

Lemma Qpower_theory : power_theory 1 Qmult Qeq Z.of_N Qpower.
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
  | Z.of_N ?n => Ncst n
  | NtoZ ?n => Ncst n
  | _ => NotConstant
  end.

Add Field Qfield : Qsft
 (decidable Qeq_bool_eq,
  completeness Qeq_eq_bool,
  constants [Qcst],
  power_tac Qpower_theory [Qpow_tac]).

(** Exemple of use: *)

Section Examples.

Section Ex1.
Let ex1 : forall x y z : Q, (x+y)*z ==  (x*z)+(y*z).
  intros.
  ring.
Defined.
End Ex1.

Section Ex2.
Let ex2 : forall x y : Q, x+y == y+x.
  intros.
  ring.
Defined.
End Ex2.

Section Ex3.
Let ex3 : forall x y z : Q, (x+y)+z == x+(y+z).
  intros.
  ring.
Defined.
End Ex3.

Section Ex4.
Let ex4 : (inject_Z 1)+(inject_Z 1)==(inject_Z 2).
  ring.
Defined.
End Ex4.

Section Ex5.
Let ex5 : 1+1 == 2#1.
  ring.
Defined.
End Ex5.

Section Ex6.
Let ex6 : (1#1)+(1#1) == 2#1.
  ring.
Defined.
End Ex6.

Section Ex7.
Let ex7 : forall x : Q, x-x== 0.
  intro.
  ring.
Defined.
End Ex7.

Section Ex8.
Let ex8 : forall x : Q, x^1 == x.
  intro.
  ring.
Defined.
End Ex8.

Section Ex9.
Let ex9 : forall x : Q, x^0 == 1.
  intro.
  ring.
Defined.
End Ex9.

Section Ex10.
Let ex10 : forall x y : Q, ~(y==0) -> (x/y)*y == x.
  intros.
  field.
  auto.
Defined.
End Ex10.

End Examples.

Lemma Qopp_plus : forall a b,  -(a+b) == -a + -b.
Proof.
  intros; ring.
Qed.

Lemma Qopp_opp : forall q, - -q==q.
Proof.
  intros; ring.
Qed.
