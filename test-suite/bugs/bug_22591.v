Set Universe Polymorphism.
Unset Collapse Sorts ToType.

Inductive list {A}  :=
| nil
| cons (h : A) (t : list).
Arguments list : clear implicits.

#[universes(polymorphic=no)] Sort Exceptional.
#[universes(polymorphic)] Axiom raise@{s;u | Exceptional -> s} : forall (A : Univ@{s;u}), A.

Definition head {A} (l : list A) : A :=
  match l with
  | cons h _ => h
  | nil => raise A
  end.
(* Failed with:
     The command has indeed failed with message:
     This expression would enforce a non-declared elimination constraint between
     Exceptional and Prop *)
