Class A := {}.
#[export] Instance a:A := {}.
#[export] Hint Extern 0 A => abstract (exact a) : typeclass_instances.
Lemma lem : A.
Proof.
  let a := constr:(_:A) in
  let b := type of a in
  exact a.
Defined.
