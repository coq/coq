
Unset Universe Minimization ToSet.

Inductive redlist A :=
   rlnil | rlcons : A -> redlist A -> redlist A.

Check redlist nat : Set.
