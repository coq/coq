Module a.
  Check let x' := _ in
             ltac:(exact x').

  Notation foo x := (let x' := x in ltac:(exact x')).

  Check foo _.
End a.

Module b.
  Notation foo x := (let x' := x in let y := (ltac:(exact I) : True) in I).
  Notation bar x := (let x' := x in let y := (I : True) in I).

  Check let x' := _ in ltac:(exact I). (* let x' := ?5 in I *)
  Check bar _. (* let x' := ?9 in let y := I in I *)
  Check foo _.
End b.
