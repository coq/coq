Require Import Ltac2.Ltac2.

Ltac2 Notation "with_loc:(" t(located(tactic)) ")" := t.

Ltac2 foo () := with_loc:(()).

Ltac2 Eval foo ().
Print foo.
