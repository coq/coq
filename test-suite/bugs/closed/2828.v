Parameter A B : Type.
Coercion POL (p : prod A B) := fst p.
Goal forall x : prod A B, A.
  intro x. Fail exact x.
