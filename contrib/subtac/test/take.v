Require Import JMeq.
Require Import List.
Require Import Coq.subtac.Utils.

Program Fixpoint take (A : Set) (l : list A) (n : nat | n <= length l) { struct l } : { l' : list A | length l' = n } :=
  match n with
  | 0 => nil
  | S p => 
    match l with
    | cons hd tl => let rest := take A tl p in cons hd rest
    | nil => _
    end
  end.

Require Import Omega.

Obligations.

Solve Obligations using (subtac_simpl ; subst ; auto with arith).

Obligations.

Obligation 3.
  destruct_call take ; subtac_simpl ; subst ; auto.
Defined.

Obligation 4.
  subst l x.
  simpl in l0.
  absurd (S p <= 0) ; omega.
Defined.

Extraction take.
