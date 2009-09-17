Notation "( x & y )" := (@existS _ _ x y) : core_scope.
Unset Printing All.
Require Import Coq.Arith.Compare_dec.

Require Import Coq.subtac.Utils.

Ltac one_simpl_hyp :=
 match goal with
 | [H : (`exist _ _ _) = _ |- _] => simpl in H
 | [H : _ = (`exist _ _ _) |- _] => simpl in H
 | [H : (`exist _ _ _) < _ |- _] => simpl in H
 | [H : _ < (`exist _ _ _) |- _] => simpl in H
 | [H : (`exist _ _ _) <= _ |- _] => simpl in H
 | [H : _ <= (`exist _ _ _) |- _] => simpl in H
 | [H : (`exist _ _ _) > _ |- _] => simpl in H
 | [H : _ > (`exist _ _ _) |- _] => simpl in H
 | [H : (`exist _ _ _) >= _ |- _] => simpl in H
 | [H : _ >= (`exist _ _ _) |- _] => simpl in H
 end.

Ltac one_simpl_subtac :=
  destruct_exists ;
  repeat one_simpl_hyp ; simpl.

Ltac simpl_subtac :=  do 3 one_simpl_subtac ; simpl.

Require Import Omega.
Require Import Wf_nat.

Program Fixpoint euclid (a : nat) (b : { b : nat | b <> O }) {wf a lt}  :
  { q : nat & { r : nat | a = b * q + r /\ r < b } } :=
  if le_lt_dec b a then let (q', r) := euclid (a - b) b in
  (S q' & r)
  else (O & a).
destruct b ; simpl_subtac.
omega.
simpl_subtac.
assert(x0 * S q' = x0 + x0 * q').
rewrite <- mult_n_Sm.
omega.
rewrite H2 ; omega.
simpl_subtac.
split ; auto with arith.
omega.
apply lt_wf.
Defined.

Check euclid_evars_proof.