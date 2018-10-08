(* Check fallback when an abbreviation is not interpretable as a pattern *)

Notation foo := Type.

Definition t :=
  match 0 with
  | S foo => foo
  | _ => 0
  end.

Notation bar := (option Type).

Definition u :=
  match 0 with
  | S bar => bar
  | _ => 0
  end.
