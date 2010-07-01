Require Export Int31.

Register array : Type -> Type as array_type.
Register make : forall A:Type, int31 -> A -> array A as array_make.
Register get : forall A:Type, array A -> int31 -> A as array_get.
Register set : forall A:Type, array A -> int31 -> A -> array A as array_set.
Register length : forall A:Type, array A -> int31 as array_length.



