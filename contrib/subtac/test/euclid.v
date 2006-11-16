Print eq_rec.
Print eq.
Inductive vector : nat -> Set :=
  | vnil : vector 0
  | vcons : nat -> forall n, vector n -> vector (S n).
Set Printing All.
Print eq.
Program Fixpoint vapp (n m : nat) (v : vector n) (w : vector m) { struct v } : vector (n + m) :=
  match v with
  | vnil => w
  | vcons a n' v' => vcons a (n' + m) (vapp n' m v' w)
  end.


Notation "( x & y )" := (@existS _ _ x y) : core_scope.
Unset Printing All.
Require Import Coq.Arith.Compare_dec.
  
Program Fixpoint euclid (a : nat) (b : { b : nat | b <> O }) {wf a lt}  :
  { q : nat & { r : nat | a = b * q + r /\ r < b } } :=
  if le_lt_dec b a then let (q', r) := euclid (a - b) b in 
  (S q' & r)
  else (O & a).

Require Import Coq.subtac.Utils.
Require Import Coq.subtac.FixSub.
Require Import Omega.
Obligations.

Obligation 1.
  intros.
  destruct_exists ; simpl in * ; auto with arith.
  omega.
Qed.

Obligation 2 of euclid.
  intros.
  destruct_exists ; simpl in * ; auto with arith.
  assert(x0 * S q' = x0 * q' + x0) by auto with arith ; omega.
Qed.

Obligation 4 of euclid.
  exact Wf_nat.lt_wf.
Qed.

Obligation 3 of euclid.
  intros.
  destruct_exists ; simpl in *.
  omega.
Qed.

Extraction Inline Fix_sub Fix_F_sub.  
Extract Inductive sigT => "pair" [ "" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extraction le_lt_dec.
Extraction euclid.


Program Definition testsig (a : nat) : { x : nat & { y : nat | x < y } } :=
  (a & S a).


Solve Obligations using auto with zarith.

Extraction testsig.
