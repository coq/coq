Class A := a: unit.
Class B (x: unit).
Axiom H: forall x: A, @B x -> x = x -> unit.
Definition Field (z: A) (m: @B z) x := (@H _ _ x) = z.
