Generalizable Variable A.
Implicit Type A : Type.

Definition works2344 : forall `(l : list A) (l' : list A), unit :=
  fix flist `(l : list A) (l' : list A) {struct l'} := tt.
Check eq_refl : @works2344 = (fix flist A l l' {struct l'} := tt).

Definition fails : forall `(l: list A), unit :=
  fix flist `(l : list A) {struct l} := tt.
Check eq_refl : @fails = (fix flist A l {struct l} := tt).
(*
Error:
Recursive definition of flist is ill-formed.
In environment
flist : forall A : Type, list A -> unit
Recursive definition on "Type"
which should be a recursive inductive type.
Recursive definition is: "fun (A : Type) (_ : list A) => tt".
*)

Definition fails2
: forall `(l : list A) (l' : list A), unit :=
  fix flist `(l : list A) (l' : list A) {struct l} := tt.
Check eq_refl : @fails2 = (fix flist A l l' {struct l} := tt).
