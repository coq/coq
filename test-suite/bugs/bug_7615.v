Set Universe Polymorphism.

Module Type S.
Parameter Inline T@{i} : Type@{i+1}.
End S.

Module F (X : S).
Definition X@{j i} : Type@{j} := X.T@{i}.
End F.

Module M.
Definition T@{i} := Type@{i}.
End M.

Module N := F(M).

Require Import Hurkens.

Fail Definition eqU@{i j} : @eq Type@{j} N.X@{i Set} Type@{i} := eq_refl.
