
Reserved Infix "$->" (at level 99).
Reserved Infix "$<~>" (at level 85).

Global Set Primitive Projections.

Class IsGraph (A : Type) :=
{
  Hom : A -> A -> Type
}.

Notation "a $-> b" := (Hom a b).

Class HasEquivs (A : Type) `{IsGraph A} :=
{
  CatEquiv : A -> A -> Type
    where "a $<~> b" := (CatEquiv a b) ;
}.

Infix "$<~>" := CatEquiv.
Axiom  cate_fun : forall `{HasEquivs} {a b}, (a $<~> b) -> (a $-> b).
Coercion cate_fun : CatEquiv >-> Hom.

Definition cate_inv {A} `{HasEquivs A} {a b : A} (f : a $<~> b) : a $-> b.
Proof.
  exact f.
Defined.
