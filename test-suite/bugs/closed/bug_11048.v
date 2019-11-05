
Inductive foo (HUGE := _) (b : HUGE) A :=
  bar (X:match _ : HUGE as T return HUGE with T => match (A : T) -> True with _ => T end end)
  : foo b A.
(* uncaught destKO *)
