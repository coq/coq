Set Universe Polymorphism.
Set Inductive Cumulativity.
Set Printing Universes.

Inductive List (A: Type) := nil | cons : A -> List A -> List A.

Section ListLift.
  Universe i j.

  Constraint i < j.

  Definition LiftL {A} : List@{i} A -> List@{j} A := fun x => x.

End ListLift.

Lemma LiftL_Lem A (l : List A) : l = LiftL l.
Proof. reflexivity. Qed.

Section ListLower.
  Universe i j.

  Constraint i < j.

  Definition LowerL {A : Type@{i}} : List@{j} A -> List@{i} A := fun x => x.

End ListLower.

Lemma LowerL_Lem@{i j} (A : Type@{j}) (l : List@{i} A) : l = LowerL l.
Proof. reflexivity. Qed.

Inductive Tp := tp : Type -> Tp.

Section TpLift.
  Universe i j.

  Constraint i < j.

  Definition LiftTp : Tp@{i} -> Tp@{j} := fun x => x.

End TpLift.

Lemma LiftC_Lem (t : Tp) : LiftTp t = t.
Proof. reflexivity. Qed.

Section TpLower.
  Universe i j.

  Constraint i < j.

  Fail Definition LowerTp : Tp@{j} -> Tp@{i} := fun x => x.

End TpLower.


Section subtyping_test.
  Universe i j.
  Constraint i < j.

  Inductive TP2 := tp2 : Type@{i} -> Type@{j} -> TP2.

End subtyping_test.