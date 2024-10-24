Module Type T.
 Parameter f : forall {A} {B : A -> Type},
   forall (f g : forall x : A, B x),
     (forall x, f x = g x) -> f = g.
End T.

Module M : T.
  Require Import TestSuite.funext.
  Definition f := @functional_extensionality_dep.
End M.

Print Assumptions M.f.
