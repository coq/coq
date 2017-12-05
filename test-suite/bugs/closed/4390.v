Module A.
Set Printing All.
Set Printing Universes.

Module M.
Section foo.
Universe i.
End foo.
End M.

Check Type@{M.i}.
(* Succeeds *)

Fail Check Type@{j}.
(* Error: Undeclared universe: j *)

Definition foo@{j} : Type@{M.i} := Type@{j}.
(* ok *)
End A.
Import A. Import M.
Set Universe Polymorphism.
Fail Universes j.
Monomorphic Universe j.
Section foo.
  Universes i.
  Constraint i < j.
  Definition foo : Type@{j} := Type@{i}.
  Definition foo' : Type@{j} := Type@{i}.
End foo.

Check eq_refl : foo@{i} = foo'@{i}.

Definition bar := foo.
Monomorphic Definition bar'@{k} := foo@{k}.

Fail Constraint j = j.
Monomorphic Constraint i = i.
