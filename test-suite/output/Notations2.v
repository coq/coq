(**********************************************************************)
(* Test call to primitive printers in presence of coercion to         *)
(* functions (cf bug #2044)                                           *)

Inductive PAIR := P (n1:nat) (n2:nat).
Coercion P : nat >-> Funclass.
Check (2 3).
