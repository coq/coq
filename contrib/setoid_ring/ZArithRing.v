(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export Ring.
Require Import ZArith_base.
Import InitialRing.

Set Implicit Arguments.

Ltac isZcst t :=
  match t with
    Z0 => true
  | Zpos ?p => isZcst p
  | Zneg ?p => isZcst p
  | xI ?p => isZcst p
  | xO ?p => isZcst p
  | xH => true
  (* injection nat -> Z *)
  | Z_of_nat ?n => isZcst n
  | O => true
  | S ?n => isZcst n
  (* injection N -> Z *)
  | Z_of_N ?n => isZcst n
  | N0 => true
  | Npos ?p => isZcst p
  (* nat -> positive *)
  | P_of_succ_nat ?n => isZcst n
  (* *)
  | _ => false
  end.
Ltac Zcst t :=
  match isZcst t with
    true => t
  | _ => NotConstant
  end.

Add Ring Zr : Zth
  (decidable Zeqb_ok, constants [Zcst], preprocess [unfold Zsucc]).
