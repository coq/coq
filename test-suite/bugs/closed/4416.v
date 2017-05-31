Goal exists x, x.
  unshelve refine (ex_intro _ _ _).
  all:match goal with |- _ _ => refine _ | _ => refine (_ _) end.
(* Error: Incorrect number of goals (expected 2 tactics). *)