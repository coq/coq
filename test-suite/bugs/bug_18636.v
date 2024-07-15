Polymorphic Axiom array@{u} : Type@{u} -> Type@{u}.
Polymorphic Axiom get : forall {A} (t : array A), A.

Lemma foo (t: array nat): True.
Proof.
assert True by abstract exact I.
assert (v := get t).
abstract exact I. (* Universe inconsistency. Cannot enforce Top.5 = Set because Set < Top.5. *)
Qed.
