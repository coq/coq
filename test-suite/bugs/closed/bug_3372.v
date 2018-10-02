Set Universe Polymorphism.
Definition hProp : Type := sigT (fun _ : Type => True).
Goal Type.
Fail exact hProp@{Set}. (* test that it fails, but is not an anomaly *)
try (exact hProp@{Set}; fail 1). (* Toplevel input, characters 15-32:
Anomaly: Uncaught exception Invalid_argument("Array.iter2", _).
Please report. *)
