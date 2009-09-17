Require Import Setoid.

Section SetoidBug.

Variable ms : Type.
Variable ms_type : ms -> Type.
Variable ms_eq : forall (A:ms), relation (ms_type A).

Variable CR : ms.

Record Ring : Type :=
{Ring_type : Type}.

Variable foo : forall (A:Ring), nat -> Ring_type A.
Variable IR : Ring.
Variable IRasCR : Ring_type IR -> ms_type CR.

Definition CRasCRing : Ring := Build_Ring (ms_type CR).

Hypothesis ms_refl : forall A x, ms_eq A x x.
Hypothesis ms_sym : forall A x y, ms_eq A x y -> ms_eq A y x.
Hypothesis ms_trans : forall A x y z, ms_eq A x y -> ms_eq A y z -> ms_eq A x z.

Add Parametric Relation A : (ms_type A) (ms_eq A)
  reflexivity proved by (ms_refl A)
  symmetry proved by (ms_sym A)
  transitivity proved by (ms_trans A)
  as ms_Setoid.

Hypothesis foobar : forall n, ms_eq CR (IRasCR (foo IR n)) (foo CRasCRing n).

Goal forall (b:ms_type CR),
 ms_eq CR (IRasCR (foo IR O)) b ->
 ms_eq CR (IRasCR (foo IR O)) b.
intros b H.
rewrite foobar.
rewrite foobar in H.
assumption.
Qed.



