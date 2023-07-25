Section S.
Context {A:Type}.
Inductive option := None | Some (a:A).
Definition map {B} (f : A -> B) (o : option) :=
  match o with
  | None => discharge.None
  | Some a => discharge.Some (f a)
  end.
End S.
