Require Import Coq.Init.Wf.

Section FixPoint.

Variable A : Set.
Variable R : A -> A -> Prop.
Hypothesis Rwf : well_founded R.
Variable P : A -> Set.

Variable F_sub : forall x:A, (forall y: { y : A | R y x }, P (proj1_sig y)) -> P x.
 
Fixpoint Fix_F_sub (x:A) (r:Acc R x) {struct r} : P x :=
   F_sub x (fun y: { y : A | R y x } => Fix_F_sub (proj1_sig y) (Acc_inv r (proj1_sig y) (proj2_sig y))).

Definition Fix_sub (x : A) := Fix_F_sub x (Rwf x).

End FixPoint.

