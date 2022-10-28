
Goal True.
Proof.
  unshelve refine (let x := _ : nat in _);[
      abstract exact 0
    | match goal with x := ?v |- _ => exact v end].
