Notation "( x & y )" := (@existS _ _ x y) : core_scope.
Unset Printing All.
Require Import Coq.Arith.Compare_dec.
  
Program Fixpoint euclid (a : nat) (b : { b : nat | b <> O }) {wf a lt}  :
  { q : nat & { r : nat | a = b * q + r /\ r < b } } :=
  if le_lt_dec b a then let (q', r) := euclid (a - b) b in 
  (S q' & r)
  else (O & a).

Require Import Omega.
Obligations.

Obligation 1.
  intros.
  simpl in * ; auto with arith.
  omega.
Defined.

Obligation 2 of euclid.
  intros.
  assert(x0 * S q' = x0 * q' + x0) by auto with arith ; omega.
Defined.

Obligation 4 of euclid.
  exact Wf_nat.lt_wf.
Defined.

Obligation 3 of euclid.
  intros.
  omega.
Qed.

Eval cbv delta [euclid_obligation_1 euclid_obligation_2] in (euclid 0).

Extraction Inline Fix_sub Fix_F_sub.  
Extract Inductive sigT => "pair" [ "" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extraction le_lt_dec.
Extraction euclid.


Program Definition testsig (a : nat) : { x : nat & { y : nat | x < y } } :=
  (a & S a).


Solve Obligations using auto with zarith.

Extraction testsig.
