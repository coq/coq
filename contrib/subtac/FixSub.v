Require Import Wf.

Section Well_founded.
Variable A : Set.
Variable R : A -> A -> Prop.
Hypothesis Rwf : well_founded R.

Section FixPoint.

Variable P : A -> Set.

Variable F_sub : forall x:A, (forall y: { y : A | R y x }, P (proj1_sig y)) -> P x.
 
Fixpoint Fix_F_sub (x : A) (r : Acc R x) {struct r} : P x :=
   F_sub x (fun y: { y : A | R y x}  => Fix_F_sub (proj1_sig y) 
   (Acc_inv r (proj1_sig y) (proj2_sig y))).

Definition Fix_sub (x : A) := Fix_F_sub x (Rwf x).

End FixPoint.

End Well_founded.

Require Import Wf_nat.
Require Import Lt.

Section Well_founded_measure.
Variable A : Set.
Variable f : A -> nat.
Definition R := fun x y => f x < f y.

Section FixPoint.

Variable P : A -> Set.

Variable F_sub : forall x:A, (forall y: { y : A | f y < f x }, P (proj1_sig y)) -> P x.
 
Fixpoint Fix_measure_F_sub (x : A) (r : Acc lt (f x)) {struct r} : P x :=
   F_sub x (fun y: { y : A | f y < f x}  => Fix_measure_F_sub (proj1_sig y) 
   (Acc_inv r (f (proj1_sig y)) (proj2_sig y))).

Definition Fix_measure_sub (x : A) := Fix_measure_F_sub x (lt_wf (f x)).

End FixPoint.

End Well_founded_measure.
