(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Eqdep_dec.
Require Import Streams.

(** * Memoization *)

(** Successive outputs of a given function [f] are stored in
    a stream in order to avoid duplicated computations. *)

Section MemoFunction.

Variable A: Type.
Variable f: nat -> A.

CoFixpoint memo_make (n:nat) : Stream A := Cons (f n) (memo_make (S n)).

Definition memo_list := memo_make 0.

Fixpoint memo_get (n:nat) (l:Stream A) : A :=
  match n with
    | O => hd l
    | S n1 => memo_get n1 (tl l)
  end.

Theorem memo_get_correct: forall n, memo_get n memo_list = f n.
Proof.
assert (F1: forall n m, memo_get n (memo_make m) = f (n + m)).
{ induction n as [| n Hrec]; try (intros m; reflexivity).
  intros m; simpl; rewrite Hrec.
  rewrite plus_n_Sm; auto. }
intros n; transitivity (f (n + 0)); try exact (F1 n 0).
rewrite <- plus_n_O; auto.
Qed.

(** Building with possible sharing using a iterator [g] :
    We now suppose in addition that [f n] is in fact the [n]-th
    iterate of a function [g].
*)

Variable g: A -> A.

Hypothesis Hg_correct: forall n, f (S n) = g (f n).

CoFixpoint imemo_make (fn:A) : Stream A :=
  let fn1 := g fn in
  Cons fn1 (imemo_make fn1).

Definition imemo_list := let f0 := f 0 in
  Cons f0 (imemo_make f0).

Theorem imemo_get_correct: forall n, memo_get n imemo_list = f n.
Proof.
assert (F1: forall n m, memo_get n (imemo_make (f m)) = f (S (n + m))).
{ induction n as [| n Hrec]; try (intros m; exact (eq_sym (Hg_correct m))).
  simpl; intros m; rewrite <- Hg_correct, Hrec, <- plus_n_Sm; auto. }
destruct n as [| n]; try reflexivity.
unfold imemo_list; simpl; rewrite F1.
rewrite <- plus_n_O; auto.
Qed.

End MemoFunction.

(** For a dependent function, the previous solution is
    reused thanks to a temporarly hiding of the dependency
    in a "container" [memo_val]. *)

Section DependentMemoFunction.

Variable A: nat -> Type.
Variable f: forall n, A n.

Inductive memo_val: Type :=
  memo_mval: forall n, A n -> memo_val.

Fixpoint is_eq (n m : nat) : {n = m} + {True} :=
  match n, m return {n = m} + {True} with
  | 0, 0 =>left True (eq_refl 0)
  | 0, S m1 => right (0 = S m1) I
  | S n1, 0 => right (S n1 = 0) I
  | S n1, S m1 =>
     match is_eq n1 m1 with
     | left H => left True (f_equal S H)
     | right _ => right (S n1 = S m1) I
     end
  end.

Definition memo_get_val n (v: memo_val): A n :=
match v with
| memo_mval m x =>
    match is_eq n m with
    | left H =>
       match H in (eq _ y) return (A y -> A n) with
        | eq_refl => fun v1 : A n => v1
       end
    | right _ => fun _ : A m => f n
    end x
end.

Let mf n :=  memo_mval n (f n).

Definition dmemo_list := memo_list _ mf.

Definition dmemo_get n l := memo_get_val n (memo_get _ n l).

Theorem dmemo_get_correct: forall n, dmemo_get n dmemo_list = f n.
Proof.
intros n; unfold dmemo_get, dmemo_list.
rewrite (memo_get_correct memo_val mf n); simpl.
case (is_eq n n); simpl; auto; intros e.
assert (e = eq_refl n).
 apply eq_proofs_unicity.
 induction x as [| x Hx]; destruct y as [| y].
 left; auto.
 right; intros HH; discriminate HH.
 right; intros HH; discriminate HH.
 case (Hx y).
   intros HH; left; case HH; auto.
 intros HH; right; intros HH1; case HH.
 injection HH1; auto.
rewrite H; auto.
Qed.

(** Finally, a version with both dependency and iterator *)

Variable g: forall n, A n -> A (S n).

Hypothesis Hg_correct: forall n, f (S n) = g n (f n).

Let mg v :=  match v with
             memo_mval n1 v1 => memo_mval (S n1) (g n1 v1) end.

Definition dimemo_list := imemo_list _ mf mg.

Theorem dimemo_get_correct: forall n, dmemo_get n dimemo_list = f n.
Proof.
intros n; unfold dmemo_get, dimemo_list.
rewrite (imemo_get_correct memo_val mf mg); simpl.
case (is_eq n n); simpl; auto; intros e.
assert (e = eq_refl n).
 apply eq_proofs_unicity.
 induction x as [| x Hx]; destruct y as [| y].
 left; auto.
 right; intros HH; discriminate HH.
 right; intros HH; discriminate HH.
 case (Hx y).
   intros HH; left; case HH; auto.
 intros HH; right; intros HH1; case HH.
 injection HH1; auto.
rewrite H; auto.
intros n1; unfold mf; rewrite Hg_correct; auto.
Qed.

End DependentMemoFunction.

(** An example with the memo function on factorial *)

(*
Require Import ZArith.
Open Scope Z_scope.

Fixpoint tfact (n: nat) :=
  match n with
   | O => 1
   | S n1 => Z.of_nat n * tfact n1
  end.

Definition lfact_list :=
  dimemo_list _ tfact (fun n z => (Z.of_nat (S  n) * z)).

Definition lfact n := dmemo_get _ tfact n lfact_list.

Theorem lfact_correct n: lfact n = tfact n.
Proof.
intros n; unfold lfact, lfact_list.
rewrite dimemo_get_correct; auto.
Qed.

Fixpoint nop p :=
  match p with
   | xH => 0
   | xI p1 => nop p1
   | xO p1 => nop p1
  end.

Fixpoint test z :=
  match z with
   | Z0 => 0
   | Zpos p1 => nop p1
   | Zneg p1 => nop p1
  end.

Time Eval vm_compute in test (lfact 2000).
Time Eval vm_compute in test (lfact 2000).
Time Eval vm_compute in test (lfact 1500).
Time Eval vm_compute in (lfact 1500).
*)

