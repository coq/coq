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
Require Import ssrbool ssrfun.
Require Import TestSuite.ssr_mini_mathcomp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* error 2 *)

Goal (exists f: Set -> nat, f nat = 0).
Proof. set (f:= fun  _:Set =>0). by exists f. Qed.

Goal (exists f: Set -> nat, f nat = 0).
Proof. set f := (fun  _:Set =>0). by exists f. Qed.
