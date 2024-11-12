From Stdlib Require Import PrimInt63 PrimArray.

Open Scope array_scope.

Module OneLevel.

Inductive foo : Set :=
  C : array foo -> foo.

Fixpoint f1 (x : foo) {struct x} : False :=
  match x with
  | C t => f1 (t.[0])
  end.

Fixpoint f2 (x : foo) {struct x} : False :=
  f2 match x with
  | C t => t.[0]
  end.

Fixpoint f3 (x : foo) {struct x} : False :=
  match x with
  | C t => f3 (PrimArray.default t)
  end.

End OneLevel.

Module TwoLevels.

Inductive foo : Set :=
  C : array (array foo) -> foo.

Fixpoint f1 (x : foo) {struct x} : False :=
  match x with
  | C t => f1 (t.[0].[0])
  end.

Fixpoint f2 (x : foo) {struct x} : False :=
  f2 match x with
  | C t => t.[0].[0]
  end.

Fixpoint f3 (x : foo) {struct x} : False :=
  match x with
  | C t => f3 (PrimArray.default (PrimArray.default t))
  end.

End TwoLevels.
