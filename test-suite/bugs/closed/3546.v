Set Primitive Projections.
Record prod A B := pair { fst : A ; snd : B }.
Arguments pair {_ _} _ _.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Definition ap11 {A B} {f g:A->B} (h:f=g) {x y:A} (p:x=y) : f x = g y.
Admitted.
Goal forall x y z w : Set, (x, y) = (z, w).
Proof.
  intros.
  apply ap11. (* Toplevel input, characters 21-25:
Error: In environment
x : Set
y : Set
z : Set
w : Set
Unable to unify "?31 ?191 = ?32 ?192" with "(x, y) = (z, w)".
 *)
