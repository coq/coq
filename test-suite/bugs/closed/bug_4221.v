(* Some test checking that interpreting binder names using ltac
   context does not accidentally break the bindings *)

Goal (forall x : nat, x = 1 -> False) -> 1 = 1 -> False.
  intros H0 x.
  lazymatch goal with
    | [ x : forall k : nat, _ |- _ ]
      => specialize (fun H0 => x 1 H0)
  end.
