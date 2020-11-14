
Primitive array := #array_type.

Definition testArray : array nat := [| 1; 2; 4 | 0 : nat |].

Definition on_array {A:Type} (x:array A) : Prop := True.

Check on_array testArray.

Check @on_array nat testArray.
