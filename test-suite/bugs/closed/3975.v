Module Type S. End S.

Module M (X:S). End M.

Module Type P (X : S).
  Print M.
  (* Used to say: Anomaly: X already exists. Please report. *)
  (* Should rather : print something :-) *)
