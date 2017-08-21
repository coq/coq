Axiom foo : Type -> Type.
Axiom bar : forall (T : Type), T -> foo T.
Arguments bar A x : rename.
About bar.
