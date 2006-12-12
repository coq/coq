Variable A : Set.
Require Import JMeq.
Require Import List.


Program Fixpoint take (l : list A) (n : nat | n <= length l) { struct l } : { l' : list A | length l' = n } :=
  match n with
  | 0 => nil
  | S p => 
    match l with
    | cons hd tl => let rest := take tl p in cons hd rest
    | nil => _
    end
  end.

Require Import Omega.

Obligations.

Solve Obligations using (subtac_simpl ; subst ; auto with arith).

Obligations.

Obligation 3.
  subtac_simpl.
  destruct_call take ; subtac_simpl ; subst ; auto.
Defined.

Obligation 4.
  subtac_simpl.
  subst l x.
  simpl in l0.
  absurd (S p <= 0) ; omega.
Defined.


Print take.

Extraction take.
