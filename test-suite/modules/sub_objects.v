Reset Initial.

Set Implicit Arguments.


Module M.
  Definition id:=[A:Set][x:A]x.

  Module Type SIG.
    Parameter idid:(A:Set)A->A.
  End SIG.

  Module N.
    Definition idid:=[A:Set][x:A](id x).
    Grammar constr constr8 := 
      not_eq [ "#"  constr7($b) ] -> [ (idid $b) ].
    Notation inc := (plus (S O)). 
  End N.

  Definition zero:=(N.idid O).

End M.

Definition zero := (M.N.idid O).
Definition jeden := (M.N.inc O).

Module Goly:=M.N.

Definition Gole_zero := (Goly.idid O).
Definition Goly_jeden := (Goly.inc O).

Module Ubrany : M.SIG := M.N.

Definition Ubrane_zero := (Ubrany.idid O).

