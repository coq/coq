Set Universe Polymorphism.

(** Tests for module subtyping of polymorphic terms *)

Module Type S.

Section Foo.

Universes i j.
Constraint i <= j.

Parameter foo : Type@{i} -> Type@{j}.

End Foo.

End S.

(** Same constraints *)

Module OK_1.

Definition foo@{i j} (A : Type@{i}) : Type@{j} := A.

End OK_1.

Module OK_1_Test : S := OK_1.

(** More general constraints *)

Module OK_2.

Inductive X@{i} : Type@{i} :=.
Definition foo@{i j} (A : Type@{i}) : Type@{j} := X@{j}.

End OK_2.

Module OK_2_Test : S := OK_2.

(** Wrong instance length *)

Module KO_1.

Definition foo@{i} (A : Type@{i}) : Type@{i} := A.

End KO_1.

Fail Module KO_Test_1 : S := KO_1.

(** Less general constraints *)

Module KO_2.

Section Foo.

Universe i j.
Constraint i < j.

Definition foo (A : Type@{i}) : Type@{j} := A.

End Foo.

End KO_2.

Fail Module KO_Test_2 : S := KO_2.

(** Less general constraints *)

Module KO_3.

Section Foo.

Universe i j.
Constraint i = j.

Definition foo (A : Type@{i}) : Type@{j} := A.

End Foo.

End KO_3.

Fail Module KO_Test_3 : S := KO_3.
