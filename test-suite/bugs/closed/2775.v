Inductive typ : forall (T:Type), list T ->  Type -> Prop :=
  | Get : forall (T:Type) (l:list T), typ T l T.


Derive Inversion inv with 
(forall (X: Type) (y: list nat), typ nat y X)  Sort Prop.
