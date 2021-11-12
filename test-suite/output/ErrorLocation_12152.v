(* Reported in #12152 *)
Goal True.
Fail intro H; auto.
Fail intros H; auto.
Abort.
