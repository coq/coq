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


(* Another interesting case: Hrec has to occurrences: one cannot be folded
   back to f while the second can. *)
Parameter g : (nat->nat)->nat->nat->nat.

Definition f (n n':nat) :=
  nat_rec (fun _ => nat -> nat)
    (fun x => x)
    (fun k Hrec => g Hrec (Hrec k))
    n n'.

Goal forall a b, f (S a) b = b.
intros.
simpl.
admit.
Qed. (* Qed will fail if simpl performs eta-expansion *)

(* Yet another example. *)

Require Import List.

Goal forall A B (a:A) l f (i:B), fold_right f i ((a :: l))=i.
simpl.
admit.
Qed. (* Qed will fail if simplification is incorrect (de Bruijn!) *)
