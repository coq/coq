(*Suppose a user wants to declare a new list-like notation with support for singletons in both 8.4 and 8.5.  If they use*)
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Import ListNotations.
Import VectorNotations.
Set Implicit Arguments.
Inductive mylist T := mynil | mycons (_ : T) (_ : mylist T).
Arguments mynil {_}, _.

Delimit Scope mylist_scope with mylist.
Bind Scope mylist_scope with mylist.
Delimit Scope vector_scope with vector.

Notation " [ ] " := mynil (format "[ ]") : mylist_scope.
Notation " [ x ] " := (mycons x mynil) : mylist_scope.
Notation " [ x ; y ; .. ; z ] " := (mycons x (mycons y .. (mycons z mynil) ..)) : mylist_scope.

Check [ ]%mylist : mylist _.
Check [ ]%list : list _.
Check []%vector : Vector.t _ _.
Check [ _ ]%mylist : mylist _.
Check [ _ ]%list : list _.
Check [ _ ]%vector : Vector.t _ _.
Check [ _ ; _ ]%list : list _.
Check [ _ ; _ ]%vector : Vector.t _ _.
Check [ _ ; _ ]%mylist : mylist _.
Check [ _ ; _ ; _ ]%list : list _.
Check [ _ ; _ ; _ ]%vector : Vector.t _ _.
Check [ _ ; _ ; _ ]%mylist : mylist _.
Check [ _ ; _ ; _ ; _ ]%list : list _.
Check [ _ ; _ ; _ ; _ ]%vector : Vector.t _ _.
Check [ _ ; _ ; _ ; _ ]%mylist : mylist _.
