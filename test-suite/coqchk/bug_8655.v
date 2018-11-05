Inductive IND2 (A:Type) (T:=fun _ : Type->Type => A) := CONS2 : IND2 A -> IND2 (T IND2).
