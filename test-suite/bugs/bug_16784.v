
Axiom P : SProp.

Fail Check list P.

Lemma foo : True.
Proof.
  unshelve refine (let x : Type := _ in _).
  refine (list _).
  exact_no_check 0.
  Fail match goal with x := ?v |- _ => let _ := type of v in idtac end. (* typing *)
  exact I.
  Fail Qed. (* kernel *)
Abort.
