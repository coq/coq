Module Pt1.

  Module M. Universe i. End M.
  Module N. Universe i. End N.
  Import M.
  Notation foo := Type@{i (* M.i??? *)}.
  Import N.
  Fail Check foo : Type@{M.i}. (* should NOT succeed *)
  Check foo : Type@{i (* N.i *)}. (* should succeed *)

  Definition bar@{i} := Type@{i}.
  Check bar : Type@{N.i}.
  Check bar : Type@{M.i}.

End Pt1.

Module Pt2.

  Module M. Universe i. Notation foo := Type@{i}. End M.

  Definition foo1 := M.foo.
  (* should succeed, currently errors undeclared universe i *)

  Definition foo2@{i} : Type@{i} := M.foo.
  (* should succeed, currently errors universe inconsistency *)

End Pt2.
