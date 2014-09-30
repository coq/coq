Notation "f1 =1 f2 :> A" := (f1 = (f2 : A))
  (at level 70, f2 at next level, A at level 90) : fun_scope.

Notation "e :? pf" := (eq_rect _ (fun X : _ => X) e _ pf)
  (no associativity, at level 90).
