Require Import ssreflect.
Goal True.
unshelve case q: (S _); auto.
exact 0.
Qed.
Goal True.
unshelve case: (S _); auto.
exact 0.
Qed.
