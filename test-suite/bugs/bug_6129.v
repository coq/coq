(* Make definition of coercions compatible with local definitions. *)

Record foo (x : Type) (y:=1) := { foo_nat :> nat }.
Record foo2 (x : Type) (y:=1) (z t: Type) := { foo_nat2 :> nat }.
Record foo3 (y:=1) (z t: Type) := { foo_nat3 :> nat }.

Check fun x : foo nat => x + 1.
Check fun x : foo2 nat nat nat => x + 1.
Check fun x : foo3 nat nat => x + 1.
