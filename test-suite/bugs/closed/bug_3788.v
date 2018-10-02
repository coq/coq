Set Implicit Arguments.
Global Set Primitive Projections.
Record Functor (C D : Type) := { object_of :> forall _ : C, D }.
Axiom path_functor_uncurried : forall C D (F G : Functor C D) (_ : sigT (fun HO : object_of F = object_of G => Set)), F = G.
Fail Lemma path_functor_uncurried_snd C D F G HO HM
: (@path_functor_uncurried C D F G (existT _ HO HM)) = HM.
