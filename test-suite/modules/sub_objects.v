Reset Initial.

Set Implicit Arguments.


Mod M.
  Definition id:=[A:Set][x:A]x.

  Modtype SIG.
    Parameter idid:(A:Set)A->A.
  EndT SIG.

  Mod N.
    Definition idid:=[A:Set][x:A](id x).
    Grammar constr constr8 := 
      not_eq [ "#"  constr7($b) ] -> [ (idid $b) ].
    Syntactic Definition inc := (plus (S O)). 
  EndM N.

  Definition zero:=(N.idid O).

EndM M.

Definition zero := (M.N.idid O).
Definition jeden := (M.N.inc O).

Mod Goly:=M.N.

Definition Gole_zero := (Goly.idid O).
Definition Goly_jeden := (Goly.inc O).

Mod Ubrany : M.SIG := M.N.

Definition Ubrane_zero := (Ubrany.idid O).

