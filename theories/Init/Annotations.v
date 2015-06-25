Definition QuotedCoercion (T T' : Type) (f : forall (_ : T), T') (x : T) := f x.
Arguments QuotedCoercion {T T'} f x.
Notation "“ x ”" := (@QuotedCoercion _ _ _ x) (at level 0, format "“ x ”").
Notation "“ x ”" := (x) (at level 0, only parsing).
