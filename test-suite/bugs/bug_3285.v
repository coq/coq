Goal True.
Proof.
match goal with
  | _ => let x := constr:(ltac:(fail)) in idtac
  | _ => idtac
end.
Abort.
