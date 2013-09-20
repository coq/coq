(* Check that Match arguments are forbidden *)
Ltac E x := apply x.
Goal True -> True.
Fail E ltac:(match goal with
        |  |- _ => intro H
        end).
