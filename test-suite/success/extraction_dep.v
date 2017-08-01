
(** Examples of code elimination inside modules during extraction *)

Require Coq.extraction.Extraction.

(** NB: we should someday check the produced code instead of
    extracting and just compiling. *)

(** 1) Without signature ... *)

Module A.
 Definition u := 0.
 Definition v := 1.
 Module B.
  Definition w := 2.
  Definition x := 3.
 End B.
End A.

Definition testA := A.u + A.B.x.

Recursive Extraction testA. (* without: v w *)
Extraction TestCompile testA.

(** 1b) Same with an Include *)

Module Abis.
 Include A.
 Definition y := 4.
End Abis.

Definition testAbis := Abis.u + Abis.y.

Recursive Extraction testAbis. (* without: A B v w x *)
Extraction TestCompile testAbis.

(** 2) With signature, we only keep elements mentionned in signature. *)

Module Type SIG.
 Parameter u : nat.
 Parameter v : nat.
End SIG.

Module Ater : SIG.
 Include A.
End Ater.

Definition testAter := Ater.u.

Recursive Extraction testAter. (* with only: u v *)
Extraction TestCompile testAter.
