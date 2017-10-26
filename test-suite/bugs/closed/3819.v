Record Op := { t : Type ; op : t -> t }.

Canonical Structure OpType : Op := Build_Op Type (fun X => X).

Lemma test1 (X:Type) : eq (op OpType X)  X.
Proof eq_refl.

Definition test2 (A:Type) : eq (op _ A)  A.
Proof eq_refl.
