(* Let doesn't respect (default) Proof using *)

(* Maybe we will want to change this behaviour someday
   but keep in mind that if we do then "bar'" should get 2 A arguments.
*)

Set Default Proof Using "Type".
Set Warnings "-opaque-let".

Section S.

  Variable A : Type.
  Variable a : A.

  Let foo : A.
  Proof. (* Default Proof Using silently ignored *)
    exact a.
  Qed.

  Definition bar := foo.

  Variable b : A.

  Let foo' : A.
  Fail Proof using a b.
    exact b.
  Qed.

  Definition bar' := foo'.

End S.

Check bar : forall A, A -> A.
Check bar' : forall A, A -> A.
