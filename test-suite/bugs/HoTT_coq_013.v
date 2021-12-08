Set Implicit Arguments.
Generalizable All Variables.

Polymorphic Variant Category (obj : Type) :=.

            Polymorphic Variant Functor objC (C : Category objC) objD (D : Category objD) :=.

            Polymorphic Definition ComposeFunctors objC C objD D objE E (G : @Functor objD D objE E) (F : @Functor objC C objD D) : Functor C E.
Admitted.

Polymorphic Definition ProductCategory objC (C : Category objC) objD (D : Category objD) : @Category (objC * objD)%type.
Admitted.

Polymorphic Definition Cat0 : Category Empty_set.
Admitted.

Set Printing Universes.

Lemma ProductLaw0 objC (C : Category objC) (F : Functor (ProductCategory C Cat0) Cat0) (G : Functor Cat0 (ProductCategory C Cat0)) x y :
  ComposeFunctors F G = x /\
  ComposeFunctors G F = y.
Proof.
  split. (* Error: Refiner was given an argument "(objC * 0)%type" of type "Type" instead of "Set". *)
Abort.
