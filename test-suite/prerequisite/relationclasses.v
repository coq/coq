Section Relation_Definition.
Variable A : Type.

Definition relation := A -> A -> Prop.

Variable R : relation.

Definition reflexive : Prop := forall x:A, R x x.
Definition transitive : Prop := forall x y z:A, R x y -> R y z -> R x z.
Definition symmetric : Prop := forall x y:A, R x y -> R y x.
Definition antisymmetric : Prop := forall x y:A, R x y -> R y x -> x = y.
End Relation_Definition.

Section Defs.
Context {A : Type}.

Class Reflexive (R : relation A) :=
  reflexivity : forall x : A, R x x.

Class Symmetric (R : relation A) :=
  symmetry : forall {x y}, R x y -> R y x.

Class Transitive (R : relation A) :=
  transitivity : forall {x y z}, R x y -> R y z -> R x z.

Class PreOrder (R : relation A) : Prop := {
  #[global] PreOrder_Reflexive :: Reflexive R | 2 ;
  #[global] PreOrder_Transitive :: Transitive R | 2 }.

Class Equivalence (R : relation A) : Prop := {
  #[global] Equivalence_Reflexive :: Reflexive R ;
  #[global] Equivalence_Symmetric :: Symmetric R ;
  #[global] Equivalence_Transitive :: Transitive R }.

#[global] Instance eq_Reflexive : Reflexive (@eq A) := @eq_refl A.
#[global] Instance eq_Symmetric : Symmetric (@eq A) := @eq_sym A.
#[global] Instance eq_Transitive : Transitive (@eq A) := @eq_trans A.
#[global] Program Instance eq_equivalence : Equivalence (@eq A) | 10.
End Defs.
