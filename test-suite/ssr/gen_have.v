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
Require Import ssrfun ssrbool TestSuite.ssr_mini_mathcomp.
Axiom daemon : False. Ltac myadmit := case: daemon.

Axiom P : nat -> Prop.
Lemma clear_test (b1 b2 : bool) : b2 = b2.
Proof.
(* wlog gH : (b3 := b2) / b2 = b3. myadmit. *)
gen have {b1} H, gH : (b3 := b2) (w := erefl 3) / b2 = b3.
  myadmit.
Fail exact (H b1).
exact (H b2 (erefl _)).
Qed.


Lemma test1 n (ngt0 : 0 < n) : P n.
gen have lt2le, /andP[H1 H2] : n ngt0 / (0 <= n) && (n != 0).
  match goal with |- is_true((0 <= n) && (n != 0)) => myadmit end.
Check (lt2le : forall n : nat, 0 < n -> (0 <= n) && (n != 0)).
Check (H1 : 0 <= n).
Check (H2 : n != 0).
myadmit.
Qed.

Lemma test2 n (ngt0 : 0 < n) : P n.
gen have _, /andP[H1 H2] : n ngt0 / (0 <= n) && (n != 0).
  match goal with |- is_true((0 <= n) && (n != 0)) => myadmit end.
lazymatch goal with
 | lt2le : forall n : nat, is_true(0 < n) -> is_true((0 <= n) && (n != 0))
    |- _ => fail "not cleared"
 | _ => idtac end.
Check (H1 : 0 <= n).
Check (H2 : n != 0).
myadmit.
Qed.

Lemma test3 n (ngt0 : 0 < n) : P n.
gen have H : n ngt0 / (0 <= n) && (n != 0).
  match goal with |- is_true((0 <= n) && (n != 0)) => myadmit end.
Check (H : forall n : nat, 0 < n -> (0 <= n) && (n != 0)).
myadmit.
Qed.

Lemma test4 n (ngt0 : 0 < n) : P n.
gen have : n ngt0 / (0 <= n) && (n != 0).
  match goal with |- is_true((0 <= n) && (n != 0)) => myadmit end.
move=> H.
Check(H : forall n : nat, 0 < n -> (0 <= n) && (n != 0)).
myadmit.
Qed.

Lemma test4bis n (ngt0 : 0 < n) : P n.
wlog suff : n ngt0 / (0 <= n) && (n != 0); last first.
  match goal with |- is_true((0 <= n) && (n != 0)) => myadmit end.
move=> H.
Check(H : forall n : nat, 0 < n -> (0 <= n) && (n != 0)).
myadmit.
Qed.

Lemma test5 n (ngt0 : 0 < n) : P n.
Fail gen have : / (0 <= n) && (n != 0).
Abort.

Lemma test6 n (ngt0 : 0 < n) : P n.
gen have : n ngt0 / (0 <= n) && (n != 0) by myadmit.
Abort.

Lemma test7 n (ngt0 : 0 < n) : P n.
Fail gen have : n / (0 <= n) && (n != 0).
Abort.

Lemma test3wlog2 n (ngt0 : 0 < n) : P n.
gen have H : (m := n) ngt0 / (0 <= m) && (m != 0).
  match goal with
    ngt0 : is_true(0 < m) |- is_true((0 <= m) && (m != 0)) => myadmit end.
Check (H : forall n : nat, 0 < n -> (0 <= n) && (n != 0)).
myadmit.
Qed.

Lemma test3wlog3 n (ngt0 : 0 < n) : P n.
gen have H : {n} (m := n) (n := 0) ngt0 / (0 <= m) && (m != n).
  match goal with
    ngt0 : is_true(n < m) |- is_true((0 <= m) && (m != n)) => myadmit end.
Check (H : forall m n : nat, n < m -> (0 <= m) && (m != n)).
myadmit.
Qed.

Lemma testw1 n (ngt0 : 0 < n) : n <= 0.
wlog H : (z := 0) (m := n) ngt0 / m != 0.
  match goal with
    |- (forall z m,
          is_true(z < m) -> is_true(m != 0) -> is_true(m <= z)) ->
       is_true(n <= 0) => myadmit end.
Check(n : nat).
Check(m : nat).
Check(z : nat).
Check(ngt0 : z < m).
Check(H : m != 0).
myadmit.
Qed.

Lemma testw2 n (ngt0 : 0 < n) : n <= 0.
wlog H : (m := n) (z := (X in n <= X)) ngt0 / m != z.
  match goal with
    |- (forall m z : nat,
          is_true(0 < m) -> is_true(m != z) -> is_true(m <= z)) ->
            is_true(n <= 0)   => idtac end.
Restart.
wlog H : (m := n) (one := (X in X <= _)) ngt0 / m != one.
  match goal with
    |- (forall m one : nat,
          is_true(one <= m) -> is_true(m != one) -> is_true(m <= 0)) ->
            is_true(n <= 0)   => idtac end.
Restart.
wlog H : {n} (m := n) (z := (X in _ <= X)) ngt0 / m != z.
  match goal with
    |- (forall m z : nat,
          is_true(0 < z) -> is_true(m != z) -> is_true(m <= 0)) ->
            is_true(n <= 0)   => idtac end.
  myadmit.
Fail Check n.
myadmit.
Qed.

Section Test.
Variable x : nat.
Definition addx y := y + x.

Lemma testw3 (m n : nat) (ngt0 : 0 < n) : n <= addx x.
wlog H : (n0 := n) (y := x) (@twoy := (id _ as X in _ <= X)) / twoy = 2 * y.
  myadmit.
myadmit.
Qed.


Definition twox := x + x.
Definition bis := twox.

Lemma testw3x n (ngt0 : 0 < n) : n + x <= twox.
wlog H : (y := x) (@twoy := (X in _ <= X)) / twoy = 2 * y.
  match goal with
    |- (forall y : nat,
         let twoy := y + y in
         twoy = 2 * y -> is_true(n + y <= twoy)) ->
       is_true(n + x <= twox) => myadmit end.
Restart.
wlog H : (y := x) (@twoy := (id _ as X in _ <= X)) / twoy = 2 * y.
  match goal with
    |- (forall y : nat,
         let twoy := twox in
         twoy = 2 * y -> is_true(n + y <= twoy)) ->
       is_true(n + x <= twox) => myadmit end.
myadmit.
Qed.

End Test.

Lemma test_in n k (def_k : k = 0) (ngtk : k < n) : P n.
rewrite -(add0n n) in {def_k k ngtk} (m := k) (def_m := def_k) (ngtm := ngtk).
rewrite def_m add0n in {ngtm} (e := erefl 0 ) (ngt0 := ngtm) => {def_m}.
myadmit.
Qed.
