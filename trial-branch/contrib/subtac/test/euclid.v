Require Import Coq.subtac.Utils.
Require Import Coq.Arith.Compare_dec.
Notation "( x & y )" := (existS _ x y) : core_scope.
  
Program Fixpoint euclid (a : nat) (b : { b : nat | b <> O }) {wf lt a}  :
  { q : nat & { r : nat | a = b * q + r /\ r < b } } :=
  if le_lt_dec b a then let (q', r) := euclid (a - b) b in 
  (S q' & r)
  else (O & a).

Require Import Omega.

Obligations.
Solve Obligations using subtac_simpl ; omega.

Next Obligation.
  assert(x0 * S q' = x0 * q' + x0) by auto with arith ; omega.
Defined.

Program Definition test_euclid : (prod nat nat) := let (q, r) := euclid 4 2 in (q, q).

Eval lazy beta zeta delta iota in test_euclid.

Program Definition testsig (a : nat) : { x : nat & { y : nat | x < y } } :=
  (a & S a).

Check testsig.
