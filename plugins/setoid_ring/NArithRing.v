(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export Ring.
Require Import BinPos BinNat.
Import InitialRing.

Set Implicit Arguments.

Ltac Ncst t :=
  match isNcst t with
    true => t
  | _ => constr:NotConstant
  end.

Add Ring Nr : Nth (decidable Neq_bool_ok, constants [Ncst]).
