Set Primitive Projections.
Set Implicit Arguments.
Set Universe Polymorphism.

Record category :=
  { ob : Type }.

Goal forall C, ob C -> ob C.
intros.
generalize dependent (ob C).
(* 1 subgoals, subgoal 1 (ID 7)

  C : category
  ============================
   forall T : Type, T -> T
(dependent evars:) *)
intros T t.
Undo 2.
generalize dependent (@ob C).
(* 1 subgoals, subgoal 1 (ID 6)

  C : category
  X : ob C
  ============================
   Type -> ob C
(dependent evars:) *)
intros T t.
(* Toplevel input, characters 9-10:
Error: No product even after head-reduction. *)
