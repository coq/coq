(* Check that Match arguments are forbidden *)
Ltac E x := apply x.
Goal True -> True.
E ltac:(match goal with
        |  |- _ => intro H
        end).
