(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Ring.
Require Import BinPos BinNat.
Import InitialRing.

Set Implicit Arguments.

Ltac Ncst t :=
  match isNcst t with
    true => t
  | _ => constr:(NotConstant)
  end.

Add Ring Nr : Nth (decidable Neqb_ok, constants [Ncst]).
