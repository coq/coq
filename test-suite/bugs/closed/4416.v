Goal exists x, x.
Unset Solve Unification Constraints.
unshelve refine (ex_intro _ _ _); match goal with _ => refine (_ _) end.
(* Error: Incorrect number of goals (expected 2 tactics). *)
