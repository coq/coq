Class A (x : True) := a : True.
Class B x (y : A x) := b : True.
Axiom pf : forall x y, B x y -> False.
Instance: B I I := I.
Goal False.
  Hint Mode A + : typeclass_instances.
  Set Typeclasses Debug.
  pose (pf _ _ _).
  Set Typeclasses Debug Verbosity 2.

  Hint Mode A - : typeclass_instances.
  pose (pf _ _ _).
Abort.
