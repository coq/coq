(* Checking correct index of implicit by pos in fixpoints *)

Fixpoint ith_default
         {default_A : nat}
         {As : list nat}
         {struct As} : Set.
