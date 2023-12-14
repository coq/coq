Fail Definition a := fix f {struct unbound} :=
  fun (t : unit) => tt.

Generalizable Variable A.
Fixpoint fails `(l : list A) {struct l} : unit := tt.
