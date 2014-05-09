Structure type : Type := Pack { ob : Type }.
Polymorphic Record category := { foo : Type }.
Definition FuncComp := Pack category.
Axiom C : category.

Check (C : ob FuncComp). (* OK *)

Canonical Structure FuncComp.

Check (C : ob FuncComp).
(* Toplevel input, characters 15-39:
Error:
The term "C" has type "category" while it is expected to have type
 "ob FuncComp". *)
