(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Test des definitions inductives imbriquees *)

Require Import List.

Inductive X : Set :=
    cons1 : list X -> X.

Inductive Y : Set :=
    cons2 : list (Y * Y) -> Y.

(* Test inductive types with local definitions *)

Inductive eq1 : forall A:Type, let B:=A in A -> Prop :=
  refl1 : eq1 True I.

Check
 fun (P : forall A : Type, let B := A in A -> Type) (f : P True I) (A : Type) =>
   let B := A in
     fun (a : A) (e : eq1 A a) =>
       match e in (eq1 A0 B0 a0) return (P A0 a0) with
       | refl1 => f
       end.

Inductive eq2 (A:Type) (a:A)
  : forall B C:Type, let D:=(A*B*C)%type in D -> Prop :=
  refl2 : eq2 A a unit bool (a,tt,true).

(* Check that induction variables are cleared even with in clause *)

Lemma foo : forall n m : nat, n + m = n + m.
Proof.
  intros; induction m as [|m] in n |- *.
  auto.
  auto.
Qed.

(* Check selection of occurrences by pattern *)

Goal forall x, S x = S (S x).   
intros.
induction (S _) in |- * at -2.
now_show (0=1).
Undo 2.
induction (S _) in |- * at 1 3.
now_show (0=1).
Undo 2.
induction (S _) in |- * at 1.
now_show (0=S (S x)).
Undo 2.
induction (S _) in |- * at 2.
now_show (S x=0).
Undo 2.
induction (S _) in |- * at 3.
now_show (S x=1).
Undo 2.
Fail induction (S _) in |- * at 4.
Abort.

