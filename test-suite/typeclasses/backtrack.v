Set Typeclasses Strict Resolution.

(* Set Typeclasses Unique Instances *)
(** This lets typeclass search assume that instance heads are unique,
    so if one matches no other need to be tried,
    avoiding backtracking (even in unique solutions mode) 
    This is on a class-by-class basis.
 *)

(* Non unique *)
Class B.
Class A.
Set Typeclasses Unique Instances.
(* Unique *)
Class D.
Class C (A : Type) := c : A.
Unset Typeclasses Unique Instances.
Instance : B -> D -> C nat := fun _ _ => 0.
Instance : A -> D -> C nat := fun _ _ => 0.
Instance : B -> C bool := fun _ => true.

Instance : forall A, C A -> C (option A) := fun A _ => None.

Set Typeclasses Debug.

Set Typeclasses Unique Solutions.
(** This forces typeclass resolution to fail if at least two solutions 
   exist to a given set of constraints. This is a global setting.
   For constraints involving assumed unique instances, it will not fail
   if two such instances could apply, however it will fail if two different
   instances of a unique class could apply.
 *)
Fail Definition foo (d d' : D) (b b' : B) (a' a'' : A) := c : nat.
Definition foo (d d' : D) (b b' : B) (a' : A) := c : nat.

Fail Definition foo' (b b' : B) := _ : B.
Unset Typeclasses Unique Solutions.
Definition foo' (b b' : B) := _ : B.

Set Typeclasses Unique Solutions.
Definition foo'' (d d' : D) := _ : D.