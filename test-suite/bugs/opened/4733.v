(* -*- coq-prog-args: ("-emacs" "-compat" "8.4") -*- *)
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
Notation " [ x ; .. ; y ] " := (mycons x .. (mycons y mynil) ..) : mylist_scope.

(** All of these should work fine in -compat 8.4 mode, just as they do in Coq 8.4.  There needs to be a way to specify notations above so that all of these [Check]s go through in both 8.4 and 8.5 *)
Check [ _ ]%mylist : mylist _.
Fail Check [ _ ]%list : list _.
Fail Check [ _ ]%vector : Vector.t _ _.
Check [ _ ; _ ]%mylist : mylist _.
Fail Check [ _ ; _ ]%list : list _.
Fail Check [ _ ; _ ]%vector : Vector.t _ _.
