Inductive M (A:Type) : Type := M'.
Axiom pi : forall (P : Prop) (p : P), Prop.
Definition test1 A (x : _) := pi A x.           (* success     *)
Fail Definition test2 A (x : A) := pi A x.           (* failure ??? *)
Fail Definition test3 A (x : A) (_ : M A) := pi A x. (* failure     *)
Fail Definition test4 A (_ : M A) (x : A) := pi A x. (* success ??? *)
