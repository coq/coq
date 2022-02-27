Declare Custom Entry example.

Module M1.
Definition stupid (x : nat) : nat := 1.
Reserved Notation " x '==' 1 " (in custom example at level 0, x constr).
Notation " x '==' 1" := (stupid x) (in custom example).
End M1.

Module M2.
Definition stupid (x : nat) : nat := 1.
Notation " x '==' 1" := (stupid x) (in custom example at level 0).
Fail Notation " x '==' 1" := (stupid x) (in custom example at level 1).
End M2.

Module M3.
Reserved Notation " x '==' 1 " (in custom example at level 55, x constr).

Notation "[[ x ]]" := x (x custom example).

Fixpoint stupid (x : nat) : nat := match x with 0 => 1 | S x => [[ x == 1 ]] end
where " x '==' 1" := (stupid x) (in custom example).

End M3.
