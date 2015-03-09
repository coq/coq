Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 3329 lines to 153 lines, then from 118 lines to 49 lines, then from 55 lines to 38 lines, then from 46 lines to 16 lines *)

Generalizable All Variables.
Set Universe Polymorphism.
Class Foo (A : Type) := {}.
Definition Baz := Foo.
Definition Bar {A B} `{Foo A, Foo B} : True.
Proof.
  Set Printing Universes.
  (* [change] should give fresh universes for each [Foo] *)
  change Foo with Baz in *.
  admit.
Defined.
Definition foo := @Bar nat.
Check @foo Set.
(* Toplevel input, characters 26-29:
Error:
The term "Set" has type "Type (* Set+1 *)" while it is expected to have type
 "Set" (Universe inconsistency: Cannot enforce Set < Set because Set = Set)). *)
