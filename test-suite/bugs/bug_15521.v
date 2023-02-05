(* apply vs rapply *)

Axiom f : forall x y, x = 0 -> x + y = 0.
Goal exists x, x = 0 /\ x = 0.
  eexists. split.
  refine (f _ _ _). (* core of rapply *)
  - reflexivity.
  - reflexivity.
Qed.
