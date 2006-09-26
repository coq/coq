(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import NArith.
Require Export Ring.
Set Implicit Arguments.

Ltac isNcst t :=
  let t := eval hnf in t in
  match t with
    N0 => constr:true
  | Npos ?p => isNcst p
  | xI ?p => isNcst p
  | xO ?p => isNcst p
  | xH => constr:true
  | _ => constr:false
  end.
Ltac Ncst t :=
  match isNcst t with
    true => t
  | _ => NotConstant
  end.

Add Ring Nr : Nth (decidable Neq_bool_ok, constants [Ncst]).
