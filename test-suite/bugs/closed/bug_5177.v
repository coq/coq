(* Bug 5177 https://coq.inria.fr/bug/5177 :
   Extraction and module type containing application and "with" *)

Module Type T.
  Parameter t: Type.
End T.

Module Type A (MT: T).
  Parameter t1: Type.
  Parameter t2: Type.
  Parameter bar: MT.t -> t1 -> t2.
End A.

Module MakeA(MT: T): A MT with Definition t1 := nat.
  Definition t1 := nat.
  Definition t2 := nat.
  Definition bar (m: MT.t) (x:t1) := x.
End MakeA.

Require Extraction.
Recursive Extraction MakeA.
Extraction TestCompile MakeA.
