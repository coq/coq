(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export Ring.
Require Import ZArith_base.
Require Import Zpow_def.

Import InitialRing.

Set Implicit Arguments.

Ltac Zcst t :=
  match isZcst t with
    true => t
  | _ => NotConstant
  end.

Ltac isZpow_coef t :=
  match t with 
  | Zpos ?p => isPcst p
  | Z0 => true
  | _ => false
  end.

Definition N_of_Z x :=
 match x with
 | Zpos p => Npos p
 | _ => N0
 end.

Ltac Zpow_tac t :=
 match isZpow_coef t with
 | true => constr:(N_of_Z t)
 | _ => constr:(NotConstant)
 end.

Ltac Zpower_neg :=
  repeat match goal with
  | [|- ?G] => 
    match G with 
    | context c [Zpower _ (Zneg _)] =>
      let t := context c [Z0] in
      change t
    end
  end.   

Add Ring Zr : Zth
  (decidable Zeqb_ok, constants [Zcst], preprocess [Zpower_neg;unfold Zsucc],
   power_tac Zpower_theory [Zpow_tac],
    (* The two following option are not needed, it is the default chose when the set of 
        coefficiant is usual ring Z *)
    div (InitialRing.Ztriv_div_th (@Eqsth Z) (@IDphi Z)),
   sign get_signZ_th).


