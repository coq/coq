Set Primitive Projections.

Record ops {T:Type} := { is_ok : T -> Prop; constant : T }.
Arguments ops : clear implicits.

Record ops_ok {T} (Ops:ops T) := { constant_ok : is_ok Ops (constant Ops) }.

Definition nat_ops : ops nat := {| is_ok := fun n => n = 1; constant := 1 |}.
Definition nat_ops_ok : ops_ok nat_ops.
Proof.
  split. cbn. apply eq_refl.
Qed.

Definition t := Eval lazy in constant_ok nat_ops nat_ops_ok.
Definition t' := Eval vm_compute in constant_ok nat_ops nat_ops_ok.
Definition t'' := Eval native_compute in constant_ok nat_ops nat_ops_ok.

Check (eq_refl t : t = t').
Check (eq_refl t : t = t'').
