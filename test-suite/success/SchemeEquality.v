(* Examples of use of Scheme Equality *)

Module A.
Definition N := nat.
Inductive list := nil | cons : N -> list -> list.
Scheme Equality for list.
End A.

Module B.
  Section A.
    Context A (eq_A:A->A->bool)
            (A_bl : forall x y, eq_A x y = true -> x = y)
            (A_lb : forall x y, x = y -> eq_A x y = true).
    Inductive I := C : A -> I.
    Scheme Equality for I.
  End A.
End B.

Module C.
  Parameter A : Type.
  Parameter eq_A : A->A->bool.
  Parameter A_bl : forall x y, eq_A x y = true -> x = y.
  Parameter A_lb : forall x y, x = y -> eq_A x y = true.
  Hint Resolve A_bl A_lb : core.
  Inductive I := C : A -> I.
  Scheme Equality for I.
  Inductive J := D : list A -> J.
  Scheme Equality for J.
End C.

(* Universe polymorphism *)
Module D.
  Set Universe Polymorphism.
  Inductive prod (A B:Type) := pair : A -> B -> prod A B.
  Scheme Equality for prod.

  (* With an indirection *)
  Inductive box A := c : A -> box A.
  Inductive prodbox (A B:Type) := pairbox : box A -> box B -> prodbox A B.
  Scheme Equality for prodbox.
End D.
