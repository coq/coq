(* -*- coq-prog-args: ("-compat" "8.4") -*- *)
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

(** Now check that we can add and then remove notations from the parser *)
(* We should be able to stick some vernacular here to remove [] from the parser *)
Fail Remove Notation "[]".
Goal True.
  (* This should not be a syntax error; before moving this file to closed, uncomment this line. *)
  (* idtac; []. *)
  constructor.
Qed.

Check { _ : _ & _ }.
Reserved Infix "&" (at level 0).
Fail Remove Infix "&".
(* Check { _ : _ & _ }. *)
