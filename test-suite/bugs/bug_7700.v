(* Abbreviations to section variables were not located *)
Section foo.
  Let x := Set.
  Notation y := x.
  Check y.
  Variable x' : Set.
  Notation y' := x'.
  Check y'.
End foo.
