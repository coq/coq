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

Axiom daemon : False. Ltac myadmit := case: daemon.

Ltac T1 x := match goal with |- _ => set t := (x in X in _ = X) end.
Ltac T2 x := first [set t := (x in RHS)].
Ltac T3 x := first [set t := (x in Y in _ = Y)|idtac].
Ltac T4 x := set t := (x in RHS); idtac.
Ltac T5 x := match goal with |- _ => set t := (x in RHS) | |- _ => idtac end.

Require Import ssrbool TestSuite.ssr_mini_mathcomp.

Open Scope nat_scope.

Lemma foo x y : x.+1 = y + x.+1.
set t := (_.+1 in RHS). match goal with |- x.+1 = y + t => rewrite /t {t} end.
set t := (x in RHS). match goal with |- x.+1 = y + t.+1 => rewrite /t {t} end.
set t := (x in _ = x). match goal with |- x.+1 = t => rewrite /t {t} end.
set t := (x in X in _ = X).
  match goal with |- x.+1 = y + t.+1 => rewrite /t {t} end.
set t := (x in RHS). match goal with |- x.+1 = y + t.+1 => rewrite /t {t} end.
set t := (y + (1 + x) as X in _ = X).
  match goal with |- x.+1 = t => rewrite /t addSn add0n {t} end.
set t := x.+1. match goal with |- t = y + t => rewrite /t {t} end.
set t := (x).+1. match goal with |- t = y + t => rewrite /t {t} end.
set t := ((x).+1 in X in _ = X).
  match goal with |- x.+1 = y + t => rewrite /t {t} end.
set t := (x.+1 in RHS). match goal with |- x.+1 = y + t => rewrite /t {t} end.
T1 (x.+1). match goal with |- x.+1 = y + t => rewrite /t {t} end.
T2 (x.+1). match goal with |- x.+1 = y + t => rewrite /t {t} end.
T3 (x.+1). match goal with |- x.+1 = y + t => rewrite /t {t} end.
T4 (x.+1). match goal with |- x.+1 = y + t => rewrite /t {t} end.
T5 (x.+1). match goal with |- x.+1 = y + t => rewrite /t {t} end.
rewrite [RHS]addnC.
  match goal with |- x.+1 = x.+1 + y => rewrite -[RHS]addnC end.
rewrite -[in RHS](@subnK 1 x.+1) //.
  match goal with |- x.+1 = y + (x.+1 - 1 + 1) => rewrite subnK // end.
have H : x.+1 = y by myadmit.
set t := _.+1 in H |- *.
  match goal with H : t = y |- t = y + t => rewrite /t {t} in H * end.
set t := (_.+1 in X in _ + X) in H |- *.
  match goal with H : x.+1 = y |- x.+1 = y + t => rewrite /t {t} in H * end.
set t := 0. match goal with t := 0 |- x.+1 = y + x.+1 => clear t end.
set t := y + _. match goal with |- x.+1 = t => rewrite /t {t} end.
set t : nat := 0. clear t.
set t : nat := (x in RHS).
  match goal with |- x.+1 = y + t.+1 => rewrite /t {t} end.
set t : nat := RHS. match goal with |- x.+1 = t => rewrite /t {t} end.
(* set t := 0 + _. *)
(* set t := (x).+1 in X in _ + X in H |-. *)
(* set t := (x).+1 in X in _ = X.*)
Admitted.
