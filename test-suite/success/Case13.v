(* Check coercions in patterns *)

Inductive I : Set :=
  C1 : nat -> I
| C2 : I -> I.

Coercion C1 : nat >-> I.

(* Coercion at the root of pattern *)
Check [x]Cases x of (C2 n) => O | O => O | (S n) => n end.

(* Coercion not at the root of pattern *)
Check [x]Cases x of (C2 O) => O | _ => O end.

(* Unification and coercions inside patterns *)
Check [x:(option nat)]Cases x of None => O | (Some O) => O | _ => O end.

(* Coercion up to delta-conversion, and unification *)
Coercion somenat := (Some nat).
Check [x]Cases x of None => O | O => O | (S n) => n end.

(* Coercions with parameters *)
Inductive listn : nat-> Set := 
  niln : (listn O) 
| consn : (n:nat)nat->(listn n) -> (listn (S n)).

Inductive I' : nat -> Set :=
  C1' : (n:nat) (listn n) -> (I' n)
| C2' : (n:nat) (I' n) -> (I' n).

Coercion C1' : listn >-> I'.
Check [x:(I' O)]Cases x of (C2' _ _) => O | niln => O | _ => O end.
Check [x:(I' O)]Cases x of (C2' _ niln) => O | _ => O end.
