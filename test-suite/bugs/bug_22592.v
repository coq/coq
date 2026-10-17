Inductive prod_R (A B C : Type) :=
| prod_R_pair_R : A -> B -> C -> prod_R A B C.

Check (fun A B => prod_R A B True) nat nat.
(* was: nat has type Set but expected Prop *)
