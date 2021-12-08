Require Coq.Lists.List Coq.Vectors.Vector.

Module A.
Import Coq.Lists.List Coq.Vectors.Vector.
Import ListNotations.
Check [ ]%list : list _.
Import VectorNotations ListNotations.
Delimit Scope vector_scope with vector.
Check [ ]%vector : Vector.t _ _.
Check []%vector : Vector.t _ _.
Check [ ]%list : list _.
Check []%list : list _.

Goal True.
  idtac; []. (* Check that vector notations don't break the [ | .. | ] syntax of Ltac *)
Abort.

Inductive mylist A := mynil | mycons (x : A) (xs : mylist A).
Delimit Scope mylist_scope with mylist.
Bind Scope mylist_scope with mylist.
Arguments mynil {_}, _.
Arguments mycons {_} _ _.
Notation " [ ] " := mynil (format "[ ]") : mylist_scope.
Notation " [ x ] " := (mycons x nil) : mylist_scope.
Notation " [ x ; y ; .. ; z ] " :=  (mycons x (mycons y .. (mycons z nil) ..)) : mylist_scope.

Locate Module VectorNotations.
Import VectorDef.VectorNotations.

Check []%vector : Vector.t _ _.
Check []%mylist : mylist _.
Check [ ]%mylist : mylist _.
Check [ ]%list : list _.
End A.
