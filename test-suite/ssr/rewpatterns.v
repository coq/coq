(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)


Require Import ssreflect.
Require Import ssrbool ssrfun TestSuite.ssr_mini_mathcomp.

Lemma test1 : forall x y (f : nat -> nat), f (x + y).+1 = f (y + x.+1).
by move=> x y f; rewrite [_.+1](addnC x.+1).
Qed.

Lemma test2 : forall x y f, x + y + f (y + x) + f (y + x) = x + y + f (y + x) + f (x + y).
by move=> x y f; rewrite {2}[in f _]addnC.
Qed.

Lemma test2' : forall x y f, true && f (x * (y + x)) = true && f(x * (x + y)).
by move=> x y f; rewrite [in f _](addnC y).
Qed.

Lemma test2'' : forall x y f, f (y + x) + f(y + x) + f(y + x)  = f(x + y) + f(y + x) + f(x + y).
by move=> x y f; rewrite {1 3}[in f _](addnC y).
Qed.

(* patterns catching bound vars not supported *)
Lemma test2_1 : forall x y f, true && (let z := x in f (z * (y + x))) = true && f(x * (x + y)).
by move=> x y f; rewrite [in f _](addnC x). (* put y when bound var will be OK *)
Qed.

Lemma test3 : forall x y f, x + f (x + y) (f (y + x) x) = x + f (x + y) (f (x + y) x).
by move=> x y f; rewrite [in X in (f _ X)](addnC y).
Qed.

Lemma test3' : forall x y f, x = y -> x + f (x + x) x + f (x + x) x =
                                      x + f (x + y) x + f (y + x) x.
by move=> x y f E; rewrite {2 3}[in X in (f X _)]E.
Qed.

Lemma test3'' : forall x y f, x = y -> x + f (x + y) x + f (x + y) x =
                                       x + f (x + y) x + f (y + y) x.
by move=> x y f E; rewrite {2}[in X in (f X _)]E.
Qed.

Lemma test4 : forall x y f, x = y -> x + f (fun _ : nat => x + x) x + f (fun _ => x + x) x =
                                     x + f (fun _       => x + y) x + f (fun _ => y + x) x.
by move=> x y f E; rewrite {2 3}[in X in (f X _)]E.
Qed.

Lemma test4' : forall x y f, x = y -> x + f (fun _ _ _ : nat => x + x) x =
                                      x + f (fun _ _ _       => x + y) x.
by move=> x y f E; rewrite {2}[in X in (f X _)]E.
Qed.

Lemma test5 : forall x y f, x = y -> x + f (y + x) x + f (y + x) x =
                                     x + f (x + y) x + f (y + x) x.
by move=> x y f E; rewrite {1}[X in (f X _)]addnC.
Qed.

Lemma test3''' : forall x y f, x = y -> x + f (x + y) x + f (x + y) (x + y) =
                                        x + f (x + y) x + f (y + y) (x + y).
by move=> x y f E; rewrite {1}[in X in (f X X)]E.
Qed.

Lemma test3'''' : forall x y f, x = y -> x + f (x + y) x + f (x + y) (x + y) =
                                         x + f (x + y) x + f (y + y) (y + y).
by move=> x y f E; rewrite [in X in (f X X)]E.
Qed.

Lemma test3x : forall x y f, y+y = x+y -> x + f (x + y) x + f (x + y) (x + y) =
                                         x + f (x + y) x + f (y + y) (y + y).
by move=> x y f E; rewrite -[X in (f X X)]E.
Qed.

Lemma test6 : forall x y (f : nat -> nat), f (x + y).+1 = f (y.+1 + x).
by move=> x y f; rewrite [(x + y) in X in (f X)]addnC.
Qed.

Lemma test7 : forall x y (f : nat -> nat), f (x + y).+1 = f (y + x.+1).
by move=> x y f; rewrite [(x.+1 + y) as X in (f X)]addnC.
Qed.

Lemma manual x y z (f : nat -> nat -> nat) : (x + y).+1 + f (x.+1 + y) (z + (x + y).+1) = 0.
Proof.
rewrite [in f _]addSn.
match goal with |- (x + y).+1 + f (x + y).+1 (z + (x + y).+1) = 0 => idtac end.
rewrite -[X in _ = X]addn0.
match goal with |- (x + y).+1 + f (x + y).+1 (z + (x + y).+1) = 0 + 0 => idtac end.
rewrite -{2}[in X in _ = X](addn0 0).
match goal with |- (x + y).+1 + f (x + y).+1 (z + (x + y).+1) = 0 + (0 + 0) => idtac end.
rewrite [_.+1 in X in f _ X](addnC x.+1).
match goal with |- (x + y).+1 + f (x + y).+1 (z + (y + x.+1)) = 0 + (0 + 0) => idtac end.
rewrite [x.+1 + y as X in f X _]addnC.
match goal with |- (x + y).+1 + f (y + x.+1) (z + (y + x.+1)) = 0 + (0 + 0) => idtac end.
Admitted.

Goal (exists x : 'I_3, x > 0).
apply: (ex_intro _ (@Ordinal _ 2 _)).
Admitted.

Goal (forall y, 1 < y < 2 -> exists x : 'I_3, x > 0).
move=> y; case/andP=> y_gt1 y_lt2; apply: (ex_intro _ (@Ordinal _ y _)).
 by apply: leq_trans y_lt2 _.
by move=> y_lt3; apply: leq_trans _ y_gt1.
Qed.

Goal (forall x y : nat, forall P : nat -> Prop, x = y -> True).
move=> x y P E.
have: P x -> P y by suff: x = y by move=> ?; congr (P _).
Admitted.

Goal forall a : bool, a -> true && a || false && a.
by move=> a ?; rewrite [true && _]/= [_ && a]/= orbC [_ || _]//=.
Qed.

Goal forall a : bool, a -> true && a || false && a.
by move=> a ?; rewrite [X in X || _]/= [X in _ || X]/= orbC [false && a as X in X || _]//=.
Qed.

Variable a : bool.
Definition f x := x || a.
Definition g x := f x.

Goal a -> g false.
by move=> Ha; rewrite [g _]/f orbC Ha.
Qed.

Goal a -> g false || g false.
move=> Ha; rewrite {2}[g _]/f orbC Ha.
match goal with |- (is_true (false || true || g false)) => done end.
Qed.

Goal a -> (a && a || true && a) && true.
by move=> Ha; rewrite -[_ || _]/(g _) andbC /= Ha [g _]/f.
Qed.

Goal a -> (a || a) && true.
by move=> Ha; rewrite -[in _ || _]/(f _) Ha andbC /f.
Qed.
