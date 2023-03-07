Set Universe Polymorphism.
Axiom A : Type.

Inductive B : A -> Type :=
| x {a} : B a
| y {a} : B a -> B a
.

Number Notation B Nat.of_num_uint Nat.to_num_uint
  (via nat mapping [[x] => O, [y] => S]) : nat_scope.

Check 0.
Check 1.
Check 2.

(* check it generates independent univs *)
Definition foo@{v v' | v <= prod.u0, v' <= prod.u1} :=
  fun (v:A@{v}) (v':A@{v'}) => (x : B v, y x : B v').

Set Printing Universes.
Print foo.
