Set Universe Polymorphism.
Definition hProp : Type := sigT (fun _ : Type => True).
Goal hProp@{Set}. (* Toplevel input, characters 15-32:
Anomaly: Uncaught exception Invalid_argument("Array.iter2", _).
Please report. *)
