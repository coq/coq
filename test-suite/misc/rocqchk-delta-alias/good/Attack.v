Unset Elimination Schemes.

Inductive bool : Set := true | false.

Module A.
  Definition x : bool := true.
  Inductive inhabited : Prop := witness : inhabited.
End A.

(* Both declarations are legitimately aliases of A's declarations. *)
Module B.
  Include A.
End B.

Inductive eq (A0 : Type) (x0 : A0) : forall _ : A0, Prop :=
| eq_refl : eq A0 x0 x0.

Inductive False : Prop := .
Inductive True : Prop := I : True.

Definition discr (b : bool) : Prop :=
  match b with
  | true => True
  | false => False
  end.

Definition alias : eq bool A.x B.x := eq_refl bool A.x.

(* This has type False after B.x's body is replaced by false. *)
Definition transported : discr B.x :=
  match alias in eq _ _ y return discr y with
  | eq_refl _ _ => I
  end.

(* This inhabits an empty inductive after B.inhabited is replaced. *)
Definition inductive_transport : B.inhabited := A.witness.
