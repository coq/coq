(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i        $Id$       i*)

Require Import RIneq.
Require Import Omega. Open Local Scope R_scope.

Lemma Rlt_R0_R2 : 0 < 2.
change 2 with (INR 2); apply lt_INR_0; apply lt_O_Sn.
Qed.

Lemma Rplus_lt_pos : forall x y:R, 0 < x -> 0 < y -> 0 < x + y.
intros.
apply Rlt_trans with x.
assumption. 
pattern x at 1 in |- *; rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
assumption.
Qed.

Lemma IZR_eq : forall z1 z2:Z, z1 = z2 -> IZR z1 = IZR z2.
intros; rewrite H; reflexivity.
Qed.

Lemma IZR_neq : forall z1 z2:Z, z1 <> z2 -> IZR z1 <> IZR z2.
intros; red in |- *; intro; elim H; apply eq_IZR; assumption.
Qed.

Ltac discrR :=
  try
   match goal with
   |  |- (?X1 <> ?X2) =>
       change 2 with (IZR 2);
       change 1 with (IZR 1);
       change 0 with (IZR 0);
       repeat
         rewrite <- plus_IZR ||
           rewrite <- mult_IZR ||
           rewrite <- Ropp_Ropp_IZR || rewrite Z_R_minus;
       apply IZR_neq; try discriminate
   end.

Ltac prove_sup0 :=
  match goal with
  |  |- (0 < 1) => apply Rlt_0_1
  |  |- (0 < ?X1) =>
      repeat
       (apply Rmult_lt_0_compat || apply Rplus_lt_pos;
         try apply Rlt_0_1 || apply Rlt_R0_R2)
  |  |- (?X1 > 0) => change (0 < X1) in |- *; prove_sup0
  end.

Ltac omega_sup :=
  change 2 with (IZR 2);
  change 1 with (IZR 1);
  change 0 with (IZR 0);
  repeat
    rewrite <- plus_IZR ||
      rewrite <- mult_IZR || rewrite <- Ropp_Ropp_IZR || rewrite Z_R_minus; 
  apply IZR_lt; omega.
  
Ltac prove_sup :=
  match goal with
  |  |- (?X1 > ?X2) => change (X2 < X1) in |- *; prove_sup
  |  |- (0 < ?X1) => prove_sup0
  |  |- (- ?X1 < 0) => rewrite <- Ropp_0; prove_sup
  |  |- (- ?X1 < - ?X2) => apply Ropp_lt_gt_contravar; prove_sup
  |  |- (- ?X1 < ?X2) => apply Rlt_trans with 0; prove_sup
  |  |- (?X1 < ?X2) => omega_sup
  | _ => idtac
  end.

Ltac Rcompute :=
  change 2 with (IZR 2);
  change 1 with (IZR 1);
  change 0 with (IZR 0);
  repeat
    rewrite <- plus_IZR ||
      rewrite <- mult_IZR || rewrite <- Ropp_Ropp_IZR || rewrite Z_R_minus; 
  apply IZR_eq; try reflexivity.
