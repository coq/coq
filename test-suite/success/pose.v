(* Test syntax *)

Goal 0=0.
pose proof (a := I).
Fail clearbody a.
epose proof (b := fun _ => eq_refl).
Fail clearbody b.
exact (b a).
Qed.
