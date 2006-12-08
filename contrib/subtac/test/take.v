Variable A : Set.
Require Import JMeq.
Require Import List.
Require Import Coq.subtac.Utils.

Program Fixpoint take (l : list A) (n : nat | n <= length l) { struct l } : { l' : list A | length l' = n } :=
  match n with
  | 0 => nil
  | S n => 
    match l with
    | cons hd tl => let rest := take tl n in cons hd rest
    | _ => _
    end
  end.
  
Require Import Omega.


Obligations.

Solve Obligations using (subtac_simpl ; subst ; auto with arith).

Obligations.

Obligation 2.
  subtac_simpl.
  subst l x.
  simpl in l0.
  absurd (S n0 <= 0) ; omega.
Defined.

Obligation 4.
  subtac_simpl.
  destruct_call take ; subtac_simpl ; subst ; auto.
Defined.

Print take.

Extraction take.
