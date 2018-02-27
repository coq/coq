(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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
       match e in (eq1 A0 a0) return (P A0 a0) with
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

(* Check use of "as" clause *)

Inductive I := C : forall x, x<0 -> I -> I.

Goal forall x:I, x=x.
intros.
induction x as [y * IHx].
change (x = x) in IHx. (* We should have IHx:x=x *)
Abort.

(* This was not working in 8.4 *)

Goal forall h:nat->nat, h 0 = h 1 -> h 1 = h 2 -> h 0 = h 2.
intros.
induction h.
2:change (n = h 1 -> n = h 2) in IHn.
Abort.

(* This was not working in 8.4 *)

Goal forall h:nat->nat, h 0 = h 1 -> h 1 = h 2 -> h 0 = h 2. 
intros h H H0.
induction h in H |- *.
Abort.

(* "at" was not granted in 8.4 in the next two examples *)

Goal forall h:nat->nat, h 0 = h 1 -> h 1 = h 2 -> h 0 = h 2. 
intros h H H0.
induction h in H at 2, H0 at 1.
change (h 0 = 0) in H.
Abort.

Goal forall h:nat->nat, h 0 = h 1 -> h 1 = h 2 -> h 0 = h 2. 
intros h H H0.
Fail induction h in H at 2 |- *. (* Incompatible occurrences *)
Abort.

(* Check generalization with dependencies in section variables *)

Section S3.
Variables x : nat.
Definition cond := x = x.
Goal cond -> x = 0.
intros H.
induction x as [|n IHn].
2:change (n = 0) in IHn. (* We don't want a generalization over cond *)
Abort.
End S3.

(* These examples show somehow arbitrary choices of generalization wrt
   to indices, when those indices are not linear. We check here 8.4
   compatibility: when an index is a subterm of a parameter of the
   inductive type, it is not generalized. *)

Inductive repr (x:nat) : nat -> Prop := reprc z : repr x z -> repr x z.

Goal forall x, 0 = x -> repr x x -> True.
intros x H1 H.
induction H.
change True in IHrepr.
Abort.

Goal forall x, 0 = S x -> repr (S x) (S x) -> True.
intros x H1 H.
induction H.
change True in IHrepr.
Abort.

Inductive repr' (x:nat) : nat -> Prop := reprc' z : repr' x (S z) -> repr' x z.

Goal forall x, 0 = x -> repr' x x -> True.
intros x H1 H.
induction H.
change True in IHrepr'.
Abort.

(* In this case, generalization was done in 8.4 and we preserve it; this
   is arbitrary choice  *)

Inductive repr'' : nat -> nat -> Prop := reprc'' x z : repr'' x z -> repr'' x z.

Goal forall x, 0 = x -> repr'' x x -> True.
intros x H1 H.
induction H.
change (0 = z -> True) in IHrepr''.
Abort.

(* Test double induction *)

(* This was failing in 8.5 and before because of a bug in the order of
   hypotheses *)

Inductive I2 : Type :=
  C2 : forall x:nat, x=x -> I2.
Goal forall a b:I2, a = b.
double induction a b.
Abort.

(* This was leaving useless hypotheses in 8.5 and before because of
   the same bug. This is a change of compatibility. *)

Inductive I3 : Prop :=
  C3 : forall x:nat, x=x -> I3.
Goal forall a b:I3, a = b.
double induction a b.
Fail clear H. (* H should have been erased *)
Abort.

(* This one had quantification in reverse order in 8.5 and before *)
(* This is a change of compatibility. *)

Goal forall m n, le m n -> le n m -> n=m.
intros m n. double induction 1 2.
3:destruct 1. (* Should be "S m0 <= m0" *)
Abort.

(* Idem *)

Goal forall m n p q, le m n -> le p q -> n+p=m+q.
intros *. double induction 1 2.
3:clear H2. (* H2 should have been erased *)
Abort.

(* This is unchanged *)

Goal forall m n:nat, n=m.
double induction m n.
Abort.

