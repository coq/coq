(* Checking computation of free vars of a term for generalization *)

Definition Decision := fun P : Prop => {P} + {~ P}.
Class SetUnfold (P Q : Prop) : Prop := Build_SetUnfold { set_unfold : P <-> Q
}.

Section Filter_Help.

  Context {A: Type}.
  Context (fold_right : forall A B : Type, (B -> A -> A) -> A -> list B -> A).
  Definition lType2 := (sigT (fun (P : A -> Prop) => forall a, Decision (P
a))).
  Definition test (X: lType2) := let (x, _) := X in x.

  Global Instance foo `{fhl1 : list lType2} m Q:
    SetUnfold (Q)
              (fold_right _ _ (fun (s : lType2) => let (P, _) := s in and (P
m)) (Q) (fhl1)).
