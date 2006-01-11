(**********************************************************************)
(* Notations for if and let (submitted by Roland Zumkeller)           *)

Notation "a ? b ; c" := (if a then b else c) (at level 10).

Check (true ? 0 ; 1).
Check if true as x return (if x then nat else bool) then 0 else true.

Notation "'proj1' t" := (let (a,_) := t in a) (at level 1).

Check (fun e : nat * nat => proj1 e).

Notation "'decomp' a 'as' x , y 'in' b" := (let (x,y) := a in b) (at level 1).

Check (decomp (true,true) as t, u in (t,u)).

(**********************************************************************)
(* Behaviour wrt to binding variables (submitted by Roland Zumkeller) *)

Notation "! A" := (forall _:nat, A) (at level 60).

Check ! (0=0).
Check forall n, n=0.
Check forall n:nat, 0=0.

(**********************************************************************)
(* Conflict between notation and notation below coercions             *)

(* Case of a printer conflict *)

Require Import BinInt.
Coercion Zpos : positive >-> Z.
Open Scope Z_scope.

  (* Check that (Zpos 3) is better printed by the printer for Z than
     by the printer for positive *)

Check (3 + Zpos 3).

(* Case of a num printer only below coercion (submitted by Georges Gonthier) *)

Open Scope nat_scope.

Inductive znat : Set := Zpos (n : nat) | Zneg (m : nat).
Coercion Zpos: nat >-> znat.
 
Delimit Scope znat_scope with znat.
Open Scope znat_scope.
 
Variable addz : znat -> znat -> znat.
Notation "z1 + z2" := (addz z1 z2) : znat_scope.

  (* Check that "3+3", where 3 is in nat and the coercion to znat is implicit,
     is printed the same way, and not "S 2 + S 2" as if numeral printing was 
     only tested with coercion still present *)

Check (3+3).

(**********************************************************************)
(* Check recursive notations                                          *)
 
Require Import List.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Check [1;2;4].
  
Reserved Notation "( x ; y , .. , z )" (at level 0).
Notation "( x ; y , .. , z )" := (pair .. (pair x y) .. z).
Check (1;2,4).
