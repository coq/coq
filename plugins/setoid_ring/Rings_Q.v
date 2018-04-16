(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Cring.
Require Export Integral_domain.

(* Rational numbers *)
Require Import QArith.

Instance Qops: (@Ring_ops Q 0%Q 1%Q Qplus Qmult Qminus Qopp Qeq).

Instance Qri : (Ring (Ro:=Qops)).
constructor.
try apply Q_Setoid. 
apply Qplus_comp. 
apply Qmult_comp. 
apply Qminus_comp. 
apply Qopp_comp.
 exact Qplus_0_l. exact Qplus_comm. apply Qplus_assoc.
 exact Qmult_1_l.  exact Qmult_1_r. apply Qmult_assoc.
 apply Qmult_plus_distr_l.  intros. apply Qmult_plus_distr_r. 
reflexivity. exact Qplus_opp_r.
Defined.

Instance Qcri: (Cring (Rr:=Qri)).
red. exact Qmult_comm. Defined.

Lemma Q_one_zero: not (Qeq 1%Q 0%Q).
unfold Qeq. simpl. auto with *. Qed.

Instance Qdi : (Integral_domain (Rcr:=Qcri)). 
constructor. 
exact Qmult_integral. exact Q_one_zero. Defined.
