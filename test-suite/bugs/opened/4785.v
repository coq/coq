Require Import Coq.Lists.List Coq.Vectors.Vector.
Import ListNotations.
Check [ ]%list : list _.
Import VectorNotations ListNotations.
Delimit Scope vector_scope with vector.
Fail Check [ ]%vector : Vector.t _ _. (* should succeed *)
Check []%vector : Vector.t _ _.
Check [ ]%list : list _.
Fail Check []%list : list _. (* should succeed *)
