
Notation "ident_to_string! x" := (
  match (fun x : Set => x) return True with x => ltac:(exact I) end) (at level 10, only parsing).


Local Notation "foo! y" := (ident_to_string! y) (y ident, only parsing, at level 10).

Goal True.
  pose (foo! bar).
Abort.
