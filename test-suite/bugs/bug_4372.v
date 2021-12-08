(* Tactic inversion was raising an anomaly because of a fake
   dependency of TypeDenote into its argument *)

Inductive expr :=
| ETrue.

Inductive IntermediateType : Set := ITbool.

Definition TypeDenote (IT : IntermediateType) : Type :=
  match IT with
  | _ => bool
  end.

Inductive ValueDenote : forall (e:expr) it, TypeDenote it -> Prop :=
| VT : ValueDenote ETrue ITbool true.

Goal forall it v, @ValueDenote ETrue it v -> True.
  intros it v H.
  inversion H.
Abort.
