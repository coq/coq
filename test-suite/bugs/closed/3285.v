Goal True.
Proof.
match goal with
  | _ => let x := constr:($(fail)$) in idtac
  | _ => idtac
end.
Abort.
