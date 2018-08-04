(* Check that instances for local definitions in evars have compatible body *)
Goal False.
Proof.
  pose (n := 1).
  evar (m:nat).
  subst n.
  pose (n := 0).
  Fail Check ?m. (* n cannot be reinterpreted with a value convertible to 1 *)
  clearbody n.
  Fail Check ?m. (* n cannot be reinterpreted with a value convertible to 1 *)
  clear n.
  pose (n := 0+1).
  Check ?m. (* Should be ok *)
Abort.
