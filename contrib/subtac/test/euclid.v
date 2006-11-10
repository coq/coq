
Notation "( x & y )" := (@existS _ _ x y) : core_scope.
Unset Printing All.
Require Import Coq.Arith.Compare_dec.
  
Program Fixpoint euclid (a : nat) (b : { b : nat | b <> O }) {wf a lt}  :
  { q : nat & { r : nat | a = b * q + r /\ r < b } } :=
  if le_lt_dec b a then let (q', r) := euclid (a - b) b in 
  (S q' & r)
  else (O & a).

Obligations.

Require Import Coq.subtac.Utils.
Require Import Coq.subtac.FixSub.
Require Import Omega.

Obligation 1.
  simpl ; intros.
  destruct_exists ; simpl in * ; auto with arith.
  omega.
Qed.

Obligation 2 of euclid.
  simpl ; intros.
  destruct_exists ; simpl in * ; auto with arith.
  assert(x0 * S q' = x0 * q' + x0) by auto with arith ; omega.
Qed.

Obligation 4 of euclid.
  exact Wf_nat.lt_wf.
Qed.

Obligation 3 of euclid.
  simpl ; intros.
  destruct_exists ; simpl in *.
  omega.
Qed.

Extraction Inline Fix_sub Fix_F_sub.  
Extract Inductive sigT => "pair" [ "" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extraction le_lt_dec.
Extraction euclid.


Program Definition testsig (a : nat) : { x : nat & { y : nat | x = y } } :=
  (a & a).


Solve Obligations using simpl ; auto.

Extraction testsig.
