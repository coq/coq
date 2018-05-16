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


Lemma test1 n : n >= 0.
Proof.
have [:s1] @h m : 'I_(n+m).+1.
  apply: Sub 0 _.
  abstract: s1 m.
  by auto.
cut (forall m, 0 < (n+m).+1); last assumption.
rewrite [_ 1 _]/= in s1 h *.
by [].
Qed.

Lemma test2 n : n >= 0.
Proof.
have [:s1] @h m : 'I_(n+m).+1 := Sub 0 (s1 m).
  move=> m; reflexivity.
cut (forall m, 0 < (n+m).+1); last assumption.
by [].
Qed.

Lemma test3 n : n >= 0.
Proof.
Fail have [:s1] @h m : 'I_(n+m).+1 by apply: (Sub 0 (s1 m)); auto.
have [:s1] @h m : 'I_(n+m).+1 by apply: (Sub 0); abstract: s1 m; auto.
cut (forall m, 0 < (n+m).+1); last assumption.
by [].
Qed.

Lemma test4 n : n >= 0.
Proof.
have @h m : 'I_(n+m).+1 by apply: (Sub 0); abstract auto.
by [].
Qed.
