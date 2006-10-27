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
Export Ring_tac.

Set Implicit Arguments.

Ltac isZcst t :=
  let t := eval hnf in t in
  match t with
    Z0 => constr:true
  | Zpos ?p => isZcst p
  | Zneg ?p => isZcst p
  | xI ?p => isZcst p
  | xO ?p => isZcst p
  | xH => constr:true
  | _ => constr:false
  end.
Ltac Zcst t :=
  match isZcst t with
    true => t
  | _ => NotConstant
  end.

Add Ring Zr : Zth
  (decidable Zeqb_ok, constants [Zcst], preprocess [unfold Zsucc]).
