Inductive list A := Node : node A -> list A
with node A := Nil | Cons : A -> list A -> node A.

Fixpoint app {A} (l1 l2 : list A) {struct l1} : list A
with app_node {A} (n1 : node A) (l2 : list A) {struct n1} : node A.
Proof.
+ destruct l1 as [n]; constructor.
  exact (app_node _ n l2).
+ destruct n1 as [|x l1].
  - destruct l2 as [n2]; exact n2.
  - exact (Cons _ x (app _ l1 l2)).
Qed.
