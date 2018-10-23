Universe u v w.
Inductive invertible {X:Type@{u}} {Y:Type} (f:X->Y) : Prop := .

Inductive FiniteT : Type -> Prop :=
  | add_finite: forall T:Type@{v}, FiniteT T -> FiniteT (option T)
  | bij_finite: forall (X:Type@{w}) (Y:Type) (f:X->Y), FiniteT X ->
    invertible f -> FiniteT Y.

Set Printing Universes.

Axiom a : False.
(*
Constraint v <= u.
Constraint v <= w.
*)
Lemma finite_subtype: forall (X:Type) (P:X->Prop),
  FiniteT X -> (forall x:X, P x \/ ~ P x) ->
  FiniteT {x:X | P x}.
Proof.
intros.
induction H.

destruct (H0 None).
elim a.

pose (g := fun (x:{x:T | P (Some x)}) =>
  match x return {x:option T | P x} with
    | exist _ x0 i => exist (fun x:option T => P x) (Some x0) i
  end).
apply bij_finite with _ g.
apply IHFiniteT.
intro; apply H0.
elim a.

pose (g := fun (x:{x:X | P (f x)}) =>
  match x with
  | exist _ x0 i => exist (fun x:Y => P x) (f x0) i
  end).
apply bij_finite with _ g.
apply IHFiniteT.
intro; apply H0.
elim a.

Qed.
