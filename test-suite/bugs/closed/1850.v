Parameter P : Type -> Type -> Type.
Notation      "e |= t --> v" := (P e t v)     (at level 100, t at level 54).
Fail Check (nat |= nat --> nat).

