(* Testing eta-expansion of elimination predicate *)

Section NATIND2.
Variable P : nat -> Type.
Variable H0 : (P O).
Variable H1 : (P (S O)).
Variable H2 : (n:nat)(P n)->(P (S (S n))).
Fixpoint nat_ind2 [n:nat] : (P n) :=
         <P>Cases n of  
                        O     => H0
                  | (S O)     => H1
                  | (S (S n)) => (H2 n (nat_ind2 n))
        end.
End NATIND2.

