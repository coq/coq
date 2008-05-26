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
