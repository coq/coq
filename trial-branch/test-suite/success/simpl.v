(* Check that inversion of names of mutual inductive fixpoints works *)
(* (cf bug #1031) *)

Inductive tree : Set :=
| node : nat -> forest -> tree  
with forest    : Set :=
| leaf : forest  
| cons : tree    -> forest   -> forest  
    .
Definition copy_of_compute_size_forest := 
fix copy_of_compute_size_forest (f:forest) : nat :=
  match f with
  | leaf => 1
  | cons t f0 => copy_of_compute_size_forest f0 + copy_of_compute_size_tree t
  end
with copy_of_compute_size_tree (t:tree) : nat :=
  match t with
  | node _ f => 1 + copy_of_compute_size_forest f
  end for copy_of_compute_size_forest
.
Eval simpl in (copy_of_compute_size_forest leaf).



