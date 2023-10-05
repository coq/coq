Class Class1 (hom : Type) (c : hom) : Type := {
    var1 : hom -> Type;
    var2 : hom;
}.

Class Class2 {h c} (C : Class1 h c) (fmap : h -> h) := {
    var3 : var1 (fmap var2);
}.

Definition var3_cast : forall {h c C fm}, Class2 C fm -> var1 (fm var2) := @var3.
