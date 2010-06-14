(**********************************************************************)
(* Test call to primitive printers in presence of coercion to         *)
(* functions (cf bug #2044)                                           *)

Inductive PAIR := P (n1:nat) (n2:nat).
Coercion P : nat >-> Funclass.
Check (2 3).

(* Check that notations with coercions to functions inserted still work *)
(* (were not working from revision 11886 to 12951) *)

Record Binop := { binop :> nat -> nat -> nat }.
Class Plusop := { plusop : Binop; zero : nat }.
Infix "[+]" := plusop (at level 40).
Instance Plus : Plusop := {| plusop := {| binop := plus |} ; zero := 0 |}.
Check 2[+]3.

(* Test bug #2091 (variable le was printed using <= !) *)

Check forall (A: Set) (le: A -> A -> Prop) (x y: A), le x y \/ le y x.

(* Test recursive notations in cases pattern *)

Remove Printing Let prod.
Check match (0,0,0) with (x,y,z) => x+y+z end.
Check let '(a,b,c) := ((2,3),4) in a.
