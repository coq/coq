Implicit Types b : bool.
Check forall b, b = b.

(* Check the type is not used if not the reserved one *)
Check forall b:nat, b = b.

(* Check full printing *)
Set Printing All.
Check forall b, b = b.
Unset Printing All.

(* Check printing of type *)
Unset Printing Use Implicit Types.
Check forall b, b = b.
Set Printing Use Implicit Types.

(* Check factorization: we give priority on factorization over implicit type *)
Check forall b c, b = c.
Check forall c b, b = c.

(* Check factorization of implicit types *)
Check forall b1 b2, b1 = b2.

(* Check in "fun" *)
Check fun b => b = b.
Check fun b c => b = c.
Check fun c b => b = c.
Check fun b1 b2 => b1 = b2.

(* Check in binders *)
Check fix f b n := match n with 0 => b | S p => f b p end.

(* Check in notations *)
Module Notation.
  Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
    (at level 200, x binder, y binder, right associativity,
    format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'") : type_scope.
  Check forall b c, b = c.
  Check forall b1 b2, b1 = b2.
End Notation.
