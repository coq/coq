Record R1 := mkR1 { r1 : bool }.
Set Universe Polymorphism.

Record R2@{i} := mkR2 { r2 : nat; _ : Type@{i} }.

Definition builder@{i j} := ( mkR1 true , mkR2@{j} 0 Type@{i} ).

Canonical xx := builder.

Check xx0@{}. Check xx1@{_ _}. Check xx@{_ _}.

Check refl_equal : r1 _ = true.
Check refl_equal : r2 _ = 0.

About xx.
About xx0.
About xx1.

Print Universes.
