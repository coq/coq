(**********************************************************************)
(* Test call to primitive printers in presence of coercion to         *)
(* functions (cf bug #2044)                                           *)

Inductive PAIR := P (n1:nat) (n2:nat).
Coercion P : nat >-> Funclass.
Check (2 3).

(* Test bug #2091 (variable le was printed using <= !) *)

Check forall (A: Set) (le: A -> A -> Prop) (x y: A), le x y \/ le y x.
