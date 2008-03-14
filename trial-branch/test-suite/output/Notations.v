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

Section A.

Notation "! A" := (forall _:nat, A) (at level 60).

Check ! (0=0).
Check forall n, n=0.
Check forall n:nat, 0=0.

End A.

(**********************************************************************)
(* Behaviour wrt to binding variables (cf bug report #1186)           *)

Section B.

Notation "# A" := (forall n:nat, n=n->A) (at level 60).
Check forall n:nat, # (n=n).

Notation "## A" := (forall n n0:nat, n=n0->A) (at level 60).
Check forall n n0:nat, ## (n=n0).

Notation "### A" :=
 (forall n n0:nat, match n with O => True | S n => n=n0 end ->A) (at level 60).
Check forall n n0:nat, ### (n=n0).

End B.

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

(* Check basic notations involving "match" *)

Section C.

Notation "'ifzero' n" := (match n with 0 => true | S _ => false end)
  (at level 0, n at level 0).
Check (ifzero 3).

Notation "'pred' n" := (match n with 0 => 0 | S n' => n' end)
  (at level 0, n at level 0).
Check (pred 3).
Check (fun n => match n with 0 => 0 | S n => n end).
Check (fun n => match n with S p as x => p | y => 0 end).

Notation "'ifn' x 'is' 'succ' n 'then' t 'else' u" := 
  (match x with O => u | S n => t end) (at level 0, u at level 0).
Check fun x => ifn x is succ n then n else 0.

End C.

(* Check correction of bug #1179 *)

Notation "1 -" := true (at level 0).
Check 1-.

(* This is another aspect of bug #1179 (raises anomaly in 8.1) *)

Require Import ZArith.
Open Scope Z_scope.
Notation "- 4" := (-2 + -2).
Check -4.

(**********************************************************************)
(* Check notations for references with activated or deactivated       *)
(* implicit arguments                                                 *)

Notation Nil := @nil.
Check Nil.

Notation NIL := nil.
Check NIL : list nat.
