Require Export Cring.

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
