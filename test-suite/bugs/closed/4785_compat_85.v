(* -*- coq-prog-args: ("-compat" "8.5") -*- *)
Require Coq.Lists.List Coq.Vectors.Vector.
Require Coq.Compat.Coq85.

Module A.
Import Coq.Lists.List Coq.Vectors.Vector.
Import ListNotations.
Check [ ]%list : list _.
Import VectorNotations ListNotations.
Delimit Scope vector_scope with vector.
Check [ ]%vector : Vector.t _ _.
Check []%vector : Vector.t _ _.
Check [ ]%list : list _.
Fail Check []%list : list _.

Goal True.
  idtac; [ ]. (* Note that vector notations break the [ | .. | ] syntax of Ltac *)
Abort.

Inductive mylist A := mynil | mycons (x : A) (xs : mylist A).
Delimit Scope mylist_scope with mylist.
Bind Scope mylist_scope with mylist.
Arguments mynil {_}, _.
Arguments mycons {_} _ _.
Notation " [] " := mynil (compat "8.5") : mylist_scope.
Notation " [ ] " := mynil (format "[ ]") : mylist_scope.
Notation " [ x ] " := (mycons x nil) : mylist_scope.
Notation " [ x ; y ; .. ; z ] " :=  (mycons x (mycons y .. (mycons z nil) ..)) : mylist_scope.

Import Coq.Compat.Coq85.
Locate Module VectorNotations.
Import VectorDef.VectorNotations.

Check []%vector : Vector.t _ _.
Check []%mylist : mylist _.
Check [ ]%mylist : mylist _.
Check [ ]%list : list _.
End A.

Module B.
Import Coq.Compat.Coq85.

Goal True.
  idtac; []. (* Check that importing the compat file doesn't break the [ | .. | ] syntax of Ltac *)
Abort.
End B.
