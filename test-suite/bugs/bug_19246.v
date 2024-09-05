Set Universe Polymorphism.

Record box@{s|u|} (A : Type@{s|u}) : Type@{s|u} :=
  pairP { fstP : A }.

Definition bt := box True.

Check bt : Prop.
