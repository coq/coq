(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Ring.
Require Import ZArith_base.
Require Import Zpow_def.

Import InitialRing.

Set Implicit Arguments.

Ltac Zcst t :=
  match isZcst t with
    true => t
  | _ => constr:(NotConstant)
  end.

Ltac isZpow_coef t :=
  match t with
  | Zpos ?p => isPcst p
  | Z0 => constr:(true)
  | _ => constr:(false)
  end.

Notation N_of_Z := Z.to_N (only parsing).

Ltac Zpow_tac t :=
 match isZpow_coef t with
 | true => constr:(N_of_Z t)
 | _ => constr:(NotConstant)
 end.

Ltac Zpower_neg :=
  repeat match goal with
  | [|- ?G] =>
    match G with
    | context c [Z.pow _ (Zneg _)] =>
      let t := context c [Z0] in
      change t
    end
  end.

Lemma Zeqb_imp_eq : forall x y, Z.eqb x y = true -> x = y.
Proof. intros x y; exact (proj1 (Z.eqb_eq x y)). Qed.

Add Ring Zr : Zth
  (decidable Zeqb_imp_eq, constants [Zcst], preprocess [Zpower_neg;unfold Z.succ],
   power_tac Zpower_theory [Zpow_tac],
    (* The following two options are not needed; they are the default choice
       when the set of coefficient is the usual ring Z *)
    div (InitialRing.Ztriv_div_th (@Eqsth Z) (@IDphi Z)),
   sign get_signZ_th).


