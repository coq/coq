(**********************************************************************)
(* Conflict between notation and notation below coercions             *)

(* Case of a printer conflict *)

From Stdlib Require Import BinInt.
Coercion Zpos : positive >-> Z.
Open Scope Z_scope.

  (* Check that (Zpos 3) is better printed by the printer for Z than
     by the printer for positive *)

Check (3 + Zpos 3).

(* Case of a num printer only below coercion (submitted by Georges Gonthier) *)

Open Scope nat_scope.

Inductive znat : Set := Zpos (n : nat) | Zneg (m : nat).
Coercion Zpos: nat >-> znat.

Declare Scope znat_scope.
Delimit Scope znat_scope with znat.
Open Scope znat_scope.

Parameter addz : znat -> znat -> znat.
Notation "z1 + z2" := (addz z1 z2) : znat_scope.

  (* Check that "3+3", where 3 is in nat and the coercion to znat is implicit,
     is printed the same way, and not "S 2 + S 2" as if numeral printing was
     only tested with coercion still present *)

Check (3+3).

(* This is another aspect of bug #1179 (raises anomaly in 8.1) *)

From Stdlib Require Import ZArith.
Open Scope Z_scope.
Notation "- 4" := (-2 + -2).
Check -4.

(**********************************************************************)
(* Check printing of notations from other modules *)

(* 1- Non imported case *)

Require TestSuite.make_notation.

Check plus.
Check S.
Check mult.
Check le.

(* 2- Imported case *)

Import make_notation.

Check plus.
Check S.
Check mult.
Check le.
