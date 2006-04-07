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

Notation "'forall' { x : A | P } , Q" :=
  (forall x:{x:A|P}, Q)
  (at level 200, x ident, right associativity).

Notation "'fun' { x : A | P } => Q" :=
  (fun x:{x:A|P} => Q)
  (at level 200, x ident, right associativity).
