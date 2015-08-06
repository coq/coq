Require Import Init.Datatypes.

(** Notations for marking coercions *)
Definition QuotedCoercion
  (T T' : Type) (f : forall (_ : T), T') (b : bool) (x : T) := f x.
Arguments QuotedCoercion {T T'} f b x.
Notation "“ x ”" := (@QuotedCoercion _ _ _ false x) (at level 0,
  format "“ x ”").
Notation "“ x ↑ T ”" := (@QuotedCoercion _ T _ true x) (at level 0,
  format "“ x  ↑  T ”").
Notation "“ x ”" := (x) (at level 0, only parsing).
