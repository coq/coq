(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(* Proof of an imperative program computing the factorial (over type Z) *)

Require Correctness.
Require Omega.
Require ZArithRing.

(* We define the factorial as a relation... *)

Inductive fact : Z -> Z -> Prop :=
    fact_0 : (fact `0` `1`)
  | fact_S : (z,f:Z) (fact z f) -> (fact (Zs z) (Zmult (Zs z) f)).

(* ...and then we prove that it contains a function *)

Lemma fact_function : (z:Z) `0 <= z` -> (EX f:Z | (fact z f)).
Proof.
Intros.
Apply natlike_ind with P:=[z:Z](EX f:Z | (fact z f)).
Split with `1`.
Exact fact_0.

Intros.
Elim H1.
Intros.
Split with `(Zs x)*x0`.
Exact (fact_S x x0 H2).

Assumption.
Save.

(* This lemma should belong to the ZArith library *)

Lemma Z_mult_1 : (x,y:Z)`x>=1`->`y>=1`->`x*y>=1`.
Proof.
Intros.
Generalize H.
Apply natlike_ind with P:=[x:Z]`x >= 1`->`x*y >= 1`.
Omega.

Intros.
Simpl.
Elim (Z_le_lt_eq_dec `0` x0 H1).
Simpl.
Unfold Zs.
Replace `(x0+1)*y` with `x0*y+y`.
Generalize H2.
Generalize `x0*y`.
Intro.
Intros.
Omega.

Ring.

Intros.
Rewrite <- b.
Omega.

Omega.
Save.

(* (fact x f) implies x>=0 and f>=1 *)

Lemma fact_pos : (x,f:Z)(fact x f)-> `x>=0` /\ `f>=1`.
Proof.
Intros.
(Elim H; Auto).
Omega.

Intros.
(Split; Try Omega).
(Apply Z_mult_1; Try Omega).
Save.

(* (fact 0 x) implies x=1 *)

Lemma fact_0_1 : (x:Z)(fact `0` x) -> `x=1`.
Proof.
Intros.
Inversion H.
Reflexivity.

Elim (fact_pos z f H1).
Intros.
(Absurd `z >= 0`; Omega).
Save.


(* We define the loop invariant : y * x! = x0! *)

Inductive invariant [y,x,x0:Z] : Prop :=
  c_inv : (f,f0:Z)(fact x f)->(fact x0 f0)->(Zmult y f)=f0
       -> (invariant y x x0).

(* The following lemma is used to prove the preservation of the invariant *)

Lemma fact_rec : (x0,x,y:Z)`0 < x` ->
    (invariant y x x0) 
 -> (invariant `x*y` (Zpred x) x0).
Proof.
Intros x0 x y H H0.
Elim H0.
Intros.
Generalize H H0 H3.
Elim H1.
Intros.
Absurd `0 < 0`; Omega.

Intros.
Apply c_inv with f:=f1 f0:=f0.
Cut `z+1+-1 = z`. Intro eq_z. Rewrite <- eq_z in H4.
Assumption.

Omega.

Assumption.

Rewrite (Zmult_sym (Zs z) y).                     
Rewrite (Zmult_assoc_r y (Zs z) f1).
Auto.
Save.


(* This one is used to prove the proof obligation at the exit of the loop *)

Lemma invariant_0 : (x,y:Z)(invariant y `0` x)->(fact x y).
Proof.
Intros.
Elim H.
Intros.
Generalize (fact_0_1 f H0).
Intro.
Rewrite H3 in H2.
Simpl in H2.
Replace y with `y*1`.
Rewrite H2.
Assumption.

Omega.
Save.


(* At last we come to the proof itself *************************************)

(* we declare two variable x and y *)

Global Variable x : Z ref.
Global Variable y : Z ref.

(* and we give the annotated program *)

Correctness factorielle 
  { `0 <= x` }
  begin
    y := 1;
    while !x <> 0 do
      { invariant `0 <= x` /\ (invariant y x x@0) as Inv
        variant x for (Zwf ZERO) }
      y := (Zmult !x !y);
      x := (Zpred !x)
    done
  end
  { (fact x@0 y) }.
Proof.
Split.
(* decreasing *)
Unfold Zwf. Unfold Zpred. Omega.
(* preservation of the invariant *)
Split.
  Unfold Zpred; Omega.
  Cut `0 < x0`. Intro Hx0.
  Decompose [and] Inv.
  Exact (fact_rec x x0 y1 Hx0 H0).
  Omega.
(* entrance of the loop *)
Split; Auto.
Elim (fact_function x Pre1). Intros.
Apply c_inv with f:=x0 f0:=x0; Auto.
Omega.
(* exit of the loop *)
Decompose [and] Inv.
Rewrite H0 in H2.
Exact (invariant_0 x y1 H2).
Save.
