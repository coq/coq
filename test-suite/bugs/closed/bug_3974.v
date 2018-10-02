Module Type S.
End S.

Module Type M (X : S).
  Fail Module P (X : S).
  (* Used to say: Anomaly: X already exists. Please report. *)
  (* Should rather say now: Error: X already exists. *)
