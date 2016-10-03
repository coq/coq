(* Check "{{" is not confused with "{" in notations *)
Reserved Notation "x {{ y }}" (at level 40).
Notation "x {{ y }}" := (x y) (only parsing).
