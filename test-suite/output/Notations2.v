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

(* Check printing of notations with mixed reserved binders (see bug #2571) *)

Implicit Type myx : bool.
Check exists myx y, myx = y.

(* Test notation for anonymous functions up to eta-expansion *)

Check fun P:nat->nat->Prop => fun x:nat => ex (P x). 

(* Test notations with binders *)

Notation "∃ x .. y , P":= (ex (fun x => .. (ex (fun y => P)) ..))
  (x binder, y binder, at level 200, right associativity,
  format "'[  ' ∃  x  ..  y ']' ,  P").

Check (∃ n p, n+p=0).

Check ∃ (a:=0) (x:nat) y (b:=1) (c:=b) (d:=2) z (e:=3) (f:=4), x+y = z+d.

Notation "∀  x .. y , P":= (forall x, .. (forall y, P) ..)
  (x binder, at level 200, right associativity).

Check (∀ n p, n+p=0).

Notation "'λ'  x .. y , P":= (fun x => .. (fun y => P) ..)
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

Check let' f x y (a:=0) z (b:bool) := x+y+z+1 in f 0 1 2.

(* In practice, only the printing rule is used here *)
(* Note: does not work for pattern *)
Module A.
Notation "f ( x )" := (f x) (at level 10, format "f ( x )").
Check fun f x => f x + S x.

Open Scope list_scope.
Notation list1 := (1::nil)%list.
Notation plus2 n := (S (S n)).
(* plus2 was not correctly printed in the two following tests in 8.3pl1 *)
Print plus2.
Check fun n => match n with list1 => 0 | _ => 2 end.
Unset Printing Allow Match Default Clause.
Check fun n => match n with list1 => 0 | _ => 2 end.
Unset Printing Factorizable Match Patterns.
Check fun n => match n with list1 => 0 | _ => 2 end.
Set Printing Allow Match Default Clause.
Set Printing Factorizable Match Patterns.

End A.

(* This one is not fully satisfactory because binders in the same type
   are re-factorized and parentheses are needed even for atomic binder

Notation "'mylet' f [ x ; .. ; y ]  :=  t 'in' u":=
  (let f := fun x => .. (fun y => t) .. in u)
  (f ident, x closed binder, y closed binder, at level 200,
   right associativity).

Check mylet f [x;y;z;(a:bool)] := x+y+z+1 in f 0 1 2.
*)

(* Check notations for functional terms which do not necessarily
   depend on their parameter *)
(* Old request mentioned again on coq-club 20/1/2012 *)

Notation "#  x : T => t" := (fun x : T => t)
  (at level 0, t at level 200, x ident).

Check # x : nat => x.
Check # _ : nat => 2.

(* Check bug 4677 *)
Check fun x (H:le x 0) => exist (le x) 0 H.

Parameters (A : Set) (x y : A) (Q : A -> A -> Prop) (conj : Q x y).
Check (exist (Q x) y conj).

(* Check bug #4854 *)
Notation "% i" := (fun i : nat => i) (at level 0, i ident).
Check %i.
Check %j.

(* Check bug raised on coq-club on Sep 12, 2016 *)

Notation "{ x , y , .. , v }" := (fun a => (or .. (or (a = x) (a = y)) .. (a = v))).
Check ({1, 2}).

(**********************************************************************)
(* Check notations of the form ".a", ".a≡", "a≡"                      *)
(* Only "a#", "a≡" and ".≡" were working properly for parsing. The    *)
(* other ones were working only for printing.                         *)

Notation "a#" := nat.
Check nat.
Check a#.

Notation "a≡" := nat.
Check nat.
Check a≡.

Notation ".≡" := nat.
Check nat.
Check .≡.

Notation ".a#" := nat.
Check nat.
Check .a#.

Notation ".a≡" := nat.
Check nat.
Check .a≡.

Notation ".α" := nat.
Check nat.
Check .α.

(* A test for #6304 *)

Module M6304.
Notation "'for' m 'from' 0 'to' N 'updating' ( s1 )  {{ b }} ;; rest" :=
  (let s1 :=
    (fix rec(n: nat) := match n with
     | 0 => s1
     | S m => let s1 := rec m in b
     end) N
  in rest)
  (at level 20).

Check fun (a b : nat) =>
  let res := 0 in
  for i from 0 to a updating (res) {{
    for j from 0 to b updating (res) {{ S res }};;
    res
  }};; res.

End M6304.
