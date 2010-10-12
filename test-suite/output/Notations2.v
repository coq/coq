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

(* Test notations with binders *)

Notation "∃  x .. y , P":=
  (ex (fun x => .. (ex (fun y => P)) ..)) (x binder, y binder, at level 200).

Check (∃ n p, n+p=0).

Notation "∀  x .. y , P":= (forall x, .. (forall y, P) ..)
  (x binder, at level 200, right associativity).

Check (∀ n p, n+p=0).

Notation "'λ'  x .. y , P":= (fun x, .. (fun y, P) ..)
  (y binder, at level 200, right associativity).

Check (λ n p, n+p=0).

Generalizable Variable A.

Check `(λ n p : A, n=p).
Check `(∃ n p : A, n=p).
Check `(∀ n p : A, n=p).

Notation "'let'' f x .. y  :=  t 'in' u":=
  (let f := fun x => .. (fun y => t) .. in u)
  (f ident, x closed binder, y closed binder, at level 200,
   right associativity).

Check let' f x y z (a:bool) := x+y+z+1 in f 0 1 2.

(* This one is not fully satisfactory because binders in the same type
   are re-factorized and parentheses are needed even for atomic binder

Notation "'mylet' f [ x ; .. ; y ]  :=  t 'in' u":=
  (let f := fun x => .. (fun y => t) .. in u)
  (f ident, x closed binder, y closed binder, at level 200,
   right associativity).

Check mylet f [x;y;z;(a:bool)] := x+y+z+1 in f 0 1 2.
*)
