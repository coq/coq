Arguments id {_} _.

Fail Record Functor (F : Type -> Type) := {
  fmap : forall A B, (A -> B) -> F A -> F B;
  fmap_identity : fmap _ _ id = id;
}.

Fail Inductive R (x:nat) := { y : R ltac:(clear x) }.

Inductive R (x:nat) := { y : bool; z : R _ }.
