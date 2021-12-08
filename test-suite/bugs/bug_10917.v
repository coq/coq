(* This was raising an anomaly *)

Definition m (h : 0 = 1) P : P 1 -> P 0 :=
  fun H => match h, H with end.
