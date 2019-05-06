Class C (A : Type) := c : A.

Hint Mode C ! : typeclass_instances.

Goal forall f : (forall A, C A -> C (list A)), True.
intros.
  Check c. (* Loops if modes are ignored. *)
Abort.
