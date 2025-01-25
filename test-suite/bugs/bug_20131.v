Inductive sFalse : SProp := .

Lemma foo: unit.
Proof.
  simple refine (let f : sFalse -> sFalse := _ in tt).
  exact (fun x => x).
Defined.
