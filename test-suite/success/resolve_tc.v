Class C := c {}.
Local Existing Instance c.

(* check that exact doesn't do the resolution *)
Lemma bad : C.
Proof.
  let x := open_constr:(_:C) in exact x.
  Fail Qed.
Unshelve.
exact _.
Qed.

Lemma foo : C.
Proof.
  let x := open_constr:(_:C) in resolve_tc x; exact x.
Qed.

(* resolve_tc doesn't focus *)
Lemma bar : C.
Proof.
  let x := open_constr:(_:C) in exact x; resolve_tc x.
Qed.
