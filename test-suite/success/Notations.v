(* Check that "where" clause behaves as if given independently of the  *)
(* definition (variant of bug #1132 submitted by Assia Mahboubi) *)

Fixpoint plus1 (n m:nat) {struct n} : nat :=
   match n with
   | O => m
   | S p => S (p+m)
   end
 where "n + m" := (plus1 n m) : nat_scope.

(* Check behaviour wrt yet empty levels (see Stephane's bug #1850) *)

Parameter P : Type -> Type -> Type -> Type.
Notation "e |= t --> v" := (P e t v)     (at level 100, t at level 54).
Check (nat |= nat --> nat).

(* Check that first non empty definition at an empty level can be of any 
   associativity *)

Definition marker := O.
Notation "x +1" := (S x) (at level 8, left associativity).
Reset marker.
Notation "x +1" := (S x) (at level 8, right associativity).

(* Check that empty levels (here 8 and 2 in pattern) are added in the
   right order *)

Notation "' 'C_' G ( A )" := (A,G) (at level 8, G at level 2).

(* Check import of notations from within a section *)

Notation "+1 x" := (S x) (at level 25, x at level 9).
Section A. Global Notation "'Z'" := O (at level 9). End A.

(* Check use of "$" (see bug #1961) *)

Notation "$ x" := (id x) (at level 30).
Check ($ 5).
