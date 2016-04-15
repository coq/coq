Unset Strict Universe Declaration.
Set Universe Polymorphism.
Record UnitSubuniverse := { a : Type@{sm} ; x : (Type@{sm} : Type@{lg}) ; inO_internal : Type@{lg} -> Type@{lg} }.
Class In (O : UnitSubuniverse@{sm lg}) (T : Type@{lg}) := in_inO_internal : inO_internal O T.
Section foo.
  Universes sm lg.
  Context (O : UnitSubuniverse@{sm lg}).
  Context {A : Type@{sm}}.
  Context (H' : forall (C : Type@{lg}) `{In@{sm lg} O C} (f : A -> C), In@{sm lg} O C).
  Fail Check (H' : forall (C : Type@{lg}) `{In@{i j} O C} (f : A -> C), In@{j i} O C).
  Fail Context (H'' : forall (C : Type@{lg}) `{In@{i j} O C} (f : A -> C), In@{j i} O C).
End foo.
