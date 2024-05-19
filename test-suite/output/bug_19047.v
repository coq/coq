CoInductive coAcc {A : Type} (R : A -> A -> Prop) (x : A) : Prop :=
| coAcc_intro : (forall y : A, R x y -> coAcc R y) -> coAcc R x.

Fail CoFixpoint coacc_rect :
  forall (A : Type) (R : A -> A -> Prop) (P : A -> Type),
  (forall x : A, (forall y : A, R x y -> coAcc R y) ->
  (forall y : A, R x y -> P y) -> P x) -> forall x : A, coAcc R x -> P x :=
  fun (A : Type) (R : A -> A -> Prop) (P : A -> Type)
  (f : (forall x : A, (forall y : A, R x y -> coAcc R y) ->
  (forall y : A, R x y -> P y) -> P x)) =>
  cofix F (x : A) (a : coAcc R x) : P x :=
  match a with
  | coAcc_intro _ _ g => f x g (fun (y : A) (r : R x y) => F y (g y r))
  end.
