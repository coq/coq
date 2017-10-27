(* -*- coq-prog-args: ("-allow-sprop"); -*- *)

Set Universe Polymorphism.

Inductive False : SProp :=.

Axiom ℙ@{} : SProp.

Definition TYPE@{i} := ℙ -> Type@{i}.
Definition PROP@{} := ℙ -> SProp.

Definition El@{i} (A : TYPE@{i}) := forall p, A p.
Definition sEl@{} (A : PROP@{}) : SProp := forall p, A p.

Definition SPropᶠ@{} := fun (p : ℙ) => SProp.

Definition sProdᶠ@{i}
  (A : TYPE@{i})
  (B : forall (p : ℙ), El A -> SProp) : PROP := fun (p : ℙ) => forall x : El A, B p x.

Definition Falseᶠ : El SPropᶠ := fun p => False.

Definition EMᶠ : sEl (sProdᶠ SPropᶠ (fun p A => ((sProdᶠ A (fun p _ => Falseᶠ p))) p)).
Proof.
Fail Admitted.
Abort.
