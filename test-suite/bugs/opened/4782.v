Record r : Type := mk_r { type : Type; cond : type -> Prop }.

Inductive p : Prop := consp : forall (e : r) (x : type e), cond e x -> p.

Goal p.
(* insert [Fail] here when the anomaly is gone, move it to success *) apply consp with (fun _ : bool => mk_r unit (fun x => True)) nil.
(* type error should be  : apply consp with (mk_r unit (fun x => True)) nil. *)
(* Instead, we get Anomaly: Uncaught exception File "pretyping/evarconv.ml", line 394, characters 4-10: Assertion failed. Please report. *)
Abort.
