Goal forall {T}(a b : T), b=a -> {c | c=b}.
intros T a b H.
Fail setoid_rewrite H.
