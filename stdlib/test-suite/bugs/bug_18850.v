From Stdlib Require Import
  Fin
  SetoidClass. (* comment out for different error message *)

Notation fin := t.

Succeed Program Definition next_fin {n}: fin (S n) -> fin (S n) :=
  fix loop (f : fin (S n)) : fin (S n) :=
    match f with
    | F1 => F1
    | FS f' => match f' with
              | F1 => F1
              | FS _ => FS (loop f')
              end
    end.
