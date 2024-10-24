Inductive any_list {A} :=
| nil : @any_list A
| cons : forall X, A -> @any_list X -> @any_list A.

Arguments nil {A}.
Arguments cons {A X}.

Notation "[]" := (@nil Type).
Notation "hd :: tl" := (cons hd tl).

Definition xs := true :: 2137 :: false :: 0 :: [].
Fail Definition ys := 0 :: xs :: xs.

(* Goal ys = ys. produced an anomaly "Unable to handle arbitrary u+k <= v constraints" *)
