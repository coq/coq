From Stdlib Require Vector.

Inductive container : Type :=
  | container_v : Vector.t container 2 -> container
  | container_0 : container.

Fixpoint test (c : container) : unit :=
  match c with
  | container_0 => tt
  | container_v v => test (Vector.nth v (Fin.FS Fin.F1))
  end.
