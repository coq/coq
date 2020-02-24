(* -*- coq-prog-args: ("-noinit"); -*- *)

(* Check that `Eval` is available without ltac. *)

Example simple_cbn := Eval cbn in (fun x:Set => x).
Example simple_cbv := Eval cbv in (fun x:Set => x).
Example simple_vm_compute := Eval vm_compute in (fun x:Set => x).
