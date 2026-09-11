Lemma foo : nat. Proof. exact 0. Qed.

Axiom bar : nat.

Eval lazy noopaques in (fun _ => 1) foo.
Fail Eval lazy noopaques in foo = foo.
Eval lazy head noopaques in foo = foo.

Fail Eval lazy noopaques in (fun x => x + x).
Eval lazy head noopaques in (fun x => x + x).

Fail Eval lazy noopaques in bar.

Require PrimInt63.

(* unapplied primitives are not considered opaque *)
Eval lazy noopaques in PrimInt63.add.
