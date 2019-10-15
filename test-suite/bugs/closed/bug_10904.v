Definition a := fun (P:SProp) (p:P) => p.

Lemma foo : (let k := a in let k' := a in fun (x:nat) y => x) = (let k := a in fun x y => y).
Proof.
  Fail reflexivity.
  match goal with |- ?l = _ => exact_no_check (eq_refl l) end.
Fail Qed.
Abort.
