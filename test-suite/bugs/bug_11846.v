Require Import TestSuite.funind.

Inductive tree : Type :=
| Node : unit -> tree.

Definition height (s : tree) : unit :=
match s with
| Node h => h
end.

Definition bal : forall l, let h := height l in tree := fun l =>
  let h := height l in
  Node h.

Set Warnings "+all".
Functional Scheme bal_ind := Induction for bal Sort Prop.
