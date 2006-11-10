
Notation "( x & y )" := (@existS _ _ x y) : core_scope.
Unset Printing All.
Require Import Coq.Arith.Compare_dec.
  
Program Fixpoint euclid (a : nat) (b : { b : nat | b <> O }) {wf a lt}  :
  { q : nat & { r : nat | a = b * q + r /\ r < b } } :=
  if le_lt_dec b a then let (q', r) := euclid (a - b) b in 
  (S q' & r)
  else (O & a).

Obligations.

Definition t := fun (Evar46 : forall a : nat, (fun y : nat => @eq nat a y) a) (a : nat) =>
@existS nat (fun x : nat => @sig nat (fun y : nat => @eq nat x y)) a
  (@exist nat (fun y : nat => @eq nat a y) a (Evar46 a)).

Program Definition testsig (a : nat) : { x : nat & { y : nat | x = y } } :=
  (a & a).

Obligation 1.
intros ; simpl ; auto.
Qed.

Solve Obligations using auto.
reflexivity.
Defined.

Extraction testsig.
Extraction sig.
Extract Inductive sig => "" [ "" ].
Extraction testsig.

Require Import Coq.Arith.Compare_dec.

Require Import Omega.

Lemma minus_eq_add : forall x y z w, y <= x -> x - y = y * z + w -> x = y * S z + w.
intros.
assert(y * S z = y * z + y).
auto.
rewrite H1.
omega.
Qed.

Program Fixpoint euclid (a : nat) (b : { b : nat | b <> O }) {wf a lt}  :
  { q : nat & { r : nat | a = b * q + r /\ r < b } } :=
  if le_lt_dec b a then let (q', r) := euclid (a - b) b in 
  (S q' & r)
  else (O & a).
intro euclid.
simpl ; intros.
Print euclid_evars.
eapply euclid_evars with euclid.
refine (euclid_evars _ _ _ euclid a Acc_a b).
; simpl ; intros.
Show Existentials.

induction b0 ; induction r.
simpl in H.
simpl.
simpl in p0.
destruct p0.
split.

apply minus_eq_add.
omega.
auto with arith.
auto.
simpl.
induction b0 ; simpl.
split ; auto.
omega.
exact (euclid a0 Acc_a0 b0).

exact (Acc_a).
auto.
auto.
Focus 1.


