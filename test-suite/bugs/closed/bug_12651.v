
Set Warnings "+implicits-in-term".
Definition thing1 : forall {A}, A -> A := fun A a => a.
Check thing1 : _ -> _.
Fail Definition thing2 : forall {A}, A -> A := fun [A] a => a.
Fail Definition thing2 : forall A, A -> A := fun {A} a => a.
