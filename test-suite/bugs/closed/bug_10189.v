Definition foo : forall (x := unit) {y : nat}, nat := fun y => y.
Check foo (y := 3). (*We fail to get implicits in the type past a let-in*)
Definition foo' : forall (x : Set) {y : nat}, nat := fun _ y => y.
Check foo' unit (y := 3). (* It works with a function binder *)

Definition bar := let f {x} : nat -> nat := fun y => x in f (x := 3).
(* Adding bar : nat -> nat gives implicits-in-term warning *)
Fail Check bar (x := 3).
(* The implicits from the type of the local definition leak to the outer term *)
