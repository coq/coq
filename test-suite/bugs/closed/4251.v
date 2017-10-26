
Inductive array : Type -> Type :=
| carray : forall A, array A.

Inductive Mtac : Type -> Prop :=
| bind : forall {A B}, Mtac A -> (A -> Mtac B) -> Mtac B
| array_make : forall {A}, A -> Mtac (array A).

Definition Ref := array.

Definition ref : forall {A}, A -> Mtac (Ref A) := 
  fun A x=> array_make x.
Check array Type.
Check fun A : Type => Ref A.

Definition abs_val (a : Type) :=
  bind (ref a) (fun r : array Type => array_make tt).
