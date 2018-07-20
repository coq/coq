(* Was raising an anomaly "already assigned a level" on the second line *)

Notation "c1 ; c2" := (c1 + c2) (only printing, at level 76, right associativity, c1 at level 76, c2 at level 76).
Notation "c1 ; c2" := (c1 + c2) (only parsing, at level 76, right associativity, c2 at level 76).
