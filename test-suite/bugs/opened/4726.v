(*The following snippet:*)

Set Universe Polymorphism.
Set Printing Universes.

Record Inj@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{j} := { inj : A }.

(*generates the following universe constraints after minimization:

Inj@{i j} : Type@{i} -> Type@{i} -> Type@{i}
(* i j |=  *)

Here, j has been substituted by i but the constraint {i = j} has been dropped.*)
Section test.
  Universes a b.
  Constraint a < b.
  Check Inj@{a b}. (* this should prbably fail *)
End test.
