Require Import TestSuite.admit.
Definition relation (A : Type) := A -> A -> Type.
Class Reflexive {A} (R : relation A) := reflexivity : forall x : A, R x x.
Axiom IsHProp : Type -> Type.
Existing Class IsHProp.
Inductive Empty : Set := .
Notation "~ x" := (x -> Empty) : type_scope.
Record hProp := BuildhProp { type :> Type ; trunc : IsHProp type }.
Arguments BuildhProp _ {_}.
Canonical Structure default_hProp := fun T P => (@BuildhProp T P).
Generalizable Variables A B f g e n.
Axiom trunc_forall : forall `{P : A -> Type}, IsHProp (forall a, P a).
Existing Instance trunc_forall.
Inductive V : Type := | set {A : Type} (f : A -> V) : V.
Axiom mem : V -> V -> hProp.
Axiom mem_induction
: forall (C : V -> hProp), (forall v, (forall x, mem x v -> C x) -> C v) -> forall v, C v.
Definition irreflexive_mem : forall x, (fun x y => ~ mem x y) x x.
Proof.
  pose (fun x => BuildhProp (~ mem x x)).
  refine (mem_induction (fun x => BuildhProp (~ mem x x)) _); simpl in *.
  admit.
