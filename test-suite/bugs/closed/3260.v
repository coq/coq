Require Import Setoid.
Goal forall m n, n = m -> n+n = m+m.
intros.
replace n with m at 2.
lazymatch goal with
|- n + m = m + m => idtac
end.
