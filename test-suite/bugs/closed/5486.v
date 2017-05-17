Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Goal forall (T : Type) (p : prod (prod T T) bool) (Fm : Set) (f : Fm) (k :
									 forall _ : T, Fm),
    @eq Fm
	(k
	   match p return T with
	   | pair p0 swap => fst p0
	   end) f.
  intros.
  (* next statement failed in Bug 5486 *)
  match goal with
  | [ |- ?f (let (a, b) := ?d in @?e a b) = ?rhs ]
    => pose (let (a, b) := d in e a b) as t0
  end.
