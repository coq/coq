From Coq Require Extraction.

Record mixin_of T0 (b : unit) (T := T0) := Mixin { _ : T0 -> let U:=T0 in U }.
Definition d := Mixin nat tt (fun x => x).

Extraction TestCompile d.
