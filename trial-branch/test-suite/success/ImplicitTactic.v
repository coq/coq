(* A Wiedijk-Cruz-Filipe style tactic for solving implicit arguments *)

(* Declare a term expression with a hole *)
Parameter quo : nat -> forall n:nat, n<>0 -> nat.
Notation "x / y" := (quo x y _) : nat_scope.

(* Declare the tactic for resolving implicit arguments still
   unresolved after type-checking; it must complete the subgoal to
   succeed *)
Declare Implicit Tactic assumption.

Goal forall n d, d<>0 -> { q:nat & { r:nat | d * q + r = n }}.
intros.
(* Here, assumption is used to solve the implicit argument of quo *)
exists (n / d).

