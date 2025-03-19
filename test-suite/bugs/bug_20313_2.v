
Module Ltac1.
  Notation "& [ , x ; y ; .. ; z ]" :=
    (match cons x (cons y .. (cons z nil) ..) return True with xs => ltac:(exact I) end)
      (only parsing).

  Check &[ , 0 ; 1 ].
End Ltac1.

Module Ltac1Fail.
  Notation "& [ , x ; y ; .. ; z ]" :=
    (match cons x (cons y .. (cons z nil) ..) return True with xs => ltac:(exact y) end)
      (only parsing).

  Fail Check &[ , 0 ; 1 ].
End Ltac1Fail.

Require Import Ltac2.Ltac2.

Module Ltac2.
  Notation "& [ , x ; y ; .. ; z ]" :=
    (match cons x (cons y .. (cons z nil) ..) return True with xs => ltac2:(exact I) end)
      (only parsing).
  Check &[ , 0 ; 1 ].
End Ltac2.

Module Ltac2Fail.
  (* it would be nice to error at Notation time instead of at use time
     but not sure how to do that with the current design of how recursive patterns are identified *)
  Notation "& [ , x ; y ; .. ; z ]" :=
    (match cons x (cons y .. (cons z nil) ..) return True with xs => ltac2:(exact $preterm:y) end)
      (only parsing).
  Fail Check &[ , 0 ; 1 ].
End Ltac2Fail.
