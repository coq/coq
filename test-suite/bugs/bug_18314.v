Section Well_founded.

 Variable A : Type.
 Variable R : A -> A -> Prop.

 Inductive Acc (x: A) : SProp :=
     Acc_intro : (forall y:A, R y x -> Acc y) -> Acc x.

 Lemma Acc_inv : forall x:A, Acc x -> forall y:A, R y x -> Acc y.
  destruct 1; trivial.
 Defined.

 Global Arguments Acc_inv [x] _ [y] _, [x] _ y _.

 Fail Polymorphic Definition Fix_F@{s|u|} (P:A -> Type@{s|u}) (F:forall {x:A}, (forall y:A, R y x -> P y) -> P x)
   := fix Fix_F {x:A} (a:Acc x) {struct a} : P x :=
     F (fun (y:A) (h:R y x) => Fix_F (Acc_inv a h)).

End Well_founded.
