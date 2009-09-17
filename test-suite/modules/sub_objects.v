Set Implicit Arguments.
Unset Strict Implicit.


Module M.
  Definition id (A : Set) (x : A) := x.

  Module Type SIG.
    Parameter idid : forall A : Set, A -> A.
  End SIG.

  Module N.
    Definition idid (A : Set) (x : A) := id x.
    (* <Warning> : Grammar is replaced by Notation *)
    Notation inc := (plus 1).
  End N.

  Definition zero := N.idid 0.

End M.

Definition zero := M.N.idid 0.
Definition jeden := M.N.inc 0.

Module Goly := M.N.

Definition Gole_zero := Goly.idid 0.
Definition Goly_jeden := Goly.inc 0.

Module Ubrany : M.SIG := M.N.

Definition Ubrane_zero := Ubrany.idid 0.
