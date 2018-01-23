Set Primitive Projections.

Record Pack (A : Type) := pack { unpack : A }.

Definition p : Pack bool.
Proof.
refine (pack _ true).
Qed.

Definition boom : unpack bool p = let u := unpack _ in u p := eq_refl.
