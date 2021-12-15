Goal True -> True.
Proof.
Fail match goal with
| [ |- ?T ] =>
  refine (ltac:(refine (fun T => T)))
end.
(* Ltac variable T is not bound to an identifier. *)
Abort.
