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
Require Import TestSuite.ssr_mini_mathcomp.

Lemma test1 : True.
have f of seq nat & nat : nat.
  exact 3.
have g of nat := 3.
have h of nat : nat := 3.
have _ : f [::] 3 = g 3 + h 4.
Admitted.
