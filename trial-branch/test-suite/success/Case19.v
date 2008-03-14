(* This used to fail in Coq version 8.1 beta due to a non variable
   universe (issued by the inductive sort-polymorphism) being sent by
   pretyping to the kernel (bug #1182) *)

Variable T : Type.
Variable x : nat*nat.

Check let (_, _) := x in sigT (fun _ : T => nat).
