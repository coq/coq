Require Export Coq.Program.Tactics Coq.Classes.SetoidTactics Coq.Classes.CMorphisms .

Set Universe Polymorphism.

Delimit Scope category_theory_scope with category_theory.
Open Scope category_theory_scope.

Infix "∧" := prod (at level 80, right associativity) : category_theory_scope.

Class Setoid A := {
  equiv : crelation A;
  setoid_equiv :> Equivalence equiv
}.

Notation "f ≈ g" := (equiv f g) (at level 79) : category_theory_scope.

Open Scope list_scope.

Generalizable All Variables.

Fixpoint list_equiv `{Setoid A} (xs ys : list A) : Type :=
  match xs, ys with
  | nil, nil => True
  | x :: xs, y :: ys => x ≈ y ∧ list_equiv xs ys
  | _, _ => False
  end.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

Program Instance list_equivalence `{Setoid A} : Equivalence list_equiv.
Next Obligation.
  repeat intro.
  induction x; simpl; split; auto.
  reflexivity.
Qed.
Next Obligation.
  repeat intro.
  generalize dependent y.
  induction x, y; simpl; intros; auto.
  destruct X; split.
    now symmetry.
  intuition.
Qed.
Next Obligation.
admit.
Defined.
