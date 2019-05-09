Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.

Definition pred (T: Type) := T -> bool.

Section SubType.

Variables (T : Type) (P : pred T).

Structure subType : Type := SubType {
  sub_sort :> Type;
  val : sub_sort -> T;
  Sub : forall x, P x = true -> sub_sort;
  rec : forall K (_ : forall x Px, K (@Sub x Px)) u, K u;
  SubK : forall x Px, val (@Sub x Px) = x
}.

Lemma vrefl : forall x, P x = true -> x = x. Proof. easy. Qed.

End SubType.

Arguments SubType {T P} sub_sort val Sub rec SubK.
Arguments vrefl {T P} x Px.

Local Notation inlined_sub_rect :=
  (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px).

Module OK.

Local Unset Primitive Projections.
Record Σ (A : Type) (P : A -> Type) : Type :=
  exist { Σ_proj1 : A;  Σ_proj2 : P Σ_proj1 }.

Definition sig_subType T (P : pred T) : subType (fun x => P x) :=
  Eval hnf in SubType _ (@Σ_proj1 T (fun x => (fun x => P x = true) x)) _ inlined_sub_rect vrefl.

End OK.

Module KO.

Record Σ (A : Type) (P : A -> Type) : Type :=
  exist { Σ_proj1 : A;  Σ_proj2 : P Σ_proj1 }.

Definition sig_subType T (P : pred T) : subType (fun x => P x) :=
  Eval hnf in SubType _ (@Σ_proj1 T (fun x => (fun x => P x = true) x)) _ inlined_sub_rect vrefl.

End KO.
