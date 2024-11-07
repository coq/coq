Class hasPt (T : Type) := Pt { pt_ : T }.
Structure ptType := Pointed {
  sort :> Type;
  class : hasPt sort
}.

Definition pt (T : ptType) := @pt_ T (class T).

Canonical nat_ptType := Pointed nat (Pt nat 0).
Canonical forall_ptType (T : Type) (U : T -> ptType) :=
  Pointed (forall t, U t) (Pt (forall t, U t) (fun t => pt (U t))).

Definition constant {T U : Type} (f : T -> U) := forall (x y : T), f x = f y.
Definition cst (T U : Type) (y : U) := fun _ : T => y.
Lemma constant_cst (T U : Type) (y : U) : constant (cst T U y).
Proof. intros x x'; reflexivity. Qed.

Goal forall {T : Type} {U : ptType}, constant (pt (T -> U)).
Proof.
intros.
exact (constant_cst _ _ _).
Qed.
