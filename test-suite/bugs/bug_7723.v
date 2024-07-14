Set Universe Polymorphism.

Module Segfault.

Inductive decision_tree : Type := .

Fixpoint first_satisfying_helper {A B} (f : A -> option B) (ls : list A) : option B
  := match ls with
     | nil => None
     | cons x xs
       => match f x with
          | Some v => Some v
          | None => first_satisfying_helper f xs
          end
     end.

Axiom admit : forall {T}, T.
Definition dtree4 : option decision_tree :=
  match first_satisfying_helper (fun pat : nat => Some pat) (cons 0 nil)
  with
  | Some _ => admit
  | None => admit
  end
.
Definition dtree'' := Eval vm_compute in dtree4. (* segfault *)

End Segfault.

Module OtherExample.

Definition bar@{i} := Type@{i}.
Definition foo@{i j} (x y z : nat) :=
  @id Type@{j} bar@{i}.
Eval vm_compute in foo.

End OtherExample.

Module LocalClosure.

Definition bar@{i} := Type@{i}.

Definition foo@{i j} (x y z : nat) :=
  @id (nat -> Type@{j}) (fun _ => Type@{i}).
Eval vm_compute in foo.

End LocalClosure.

Module QVar.

  Definition bar@{q|i|} := Type@{q|i}.

  Definition gbar@{q1 q2|i j|} := bar@{q2|i}.

  Eval vm_compute in gbar.

  Definition gprop := Eval vm_compute in gbar@{Type Prop|Set Set}.
  Check eq_refl : gprop = Prop.

End QVar.

Require Import TestSuite.hurkens.
Polymorphic Inductive unit := tt.

Polymorphic Definition foo :=
  let x := id tt in (x, x, Type).

Lemma bad : False.
  refine (TypeNeqSmallType.paradox (snd foo) _).
  vm_compute.
  Fail reflexivity.
Abort.
