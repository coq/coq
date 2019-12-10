
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Module Export Logic.

  Set Universe Polymorphism.

  Inductive Empty : Set :=.

  Cumulative Inductive Id@{i} {A : Type@{i}} (a : A) : A -> Type@{i} :=
    id_refl : Id a a.

  Module Export Id_Notations.
    Notation " x = y " := (@Id _ x y) : type_scope.
  End Id_Notations.

  Cumulative Inductive sum@{i} (X : Type@{i}) (B : Type@{i}) :=
  | inl : X -> X + B
  | inr : B -> X + B
  where " A + B " := (sum A B) : type_scope.
  Arguments inr{A} {B} _  : rename.

End Logic.

Class EqDec@{i|Set <= i} (A : Type@{i}) := eq_dec : forall x y : A, sum@{i} (x = y) (x = y -> Empty).
Universe  i.
Context {A : Type@{i}} `{EqDec A}.

Variable x : A.
Let nu {y:A} (u:x = y) : x = y.
  admit.
Defined.

Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
  intros.
  unfold nu in |- *.
  case (eq_dec x y).
  admit.
  intros.
  Check e : x=y -> Empty.
Abort.
