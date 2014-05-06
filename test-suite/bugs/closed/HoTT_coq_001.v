Record Foo : Set :=
  {
    A' : nat;
    A : Prop := (A' = 0)
  }. (* Anomaly: Uncaught exception Reduction.NotConvertible. Please report. *)
