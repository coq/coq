(* Print Assumptions reuses traversals across queries in one environment.
   Every inductive and constructor of a mutual block carries the block's
   dependencies and its typing flags, so reaching one member through an
   earlier query's traversal must still account for all of them. *)

Module UnsafeHierarchy.
  Unset Universe Checking.
  Inductive bad : Type := C1 | C2.
  Set Universe Checking.
  Definition useC1 := C1.
  Print Assumptions useC1.
  Print Assumptions useC1.
  Print Assumptions bad.
End UnsafeHierarchy.

Module UnsafeMutual.
  Unset Universe Checking.
  Inductive tree : Type := leaf : tree | node : forest -> tree
  with forest : Type := nil_f : forest | cons_f : tree -> forest -> forest.
  Set Universe Checking.
  Definition use_leaf := leaf.
  Definition use_forest := nil_f.
  Print Assumptions use_leaf.
  Print Assumptions use_forest.
  Print Assumptions use_leaf.
  Print Assumptions cons_f.
End UnsafeMutual.

Module DefaultFlags.
  Axiom ax : nat.
  Inductive ev : nat -> Prop :=
  | ev0 : ev 0
  | evS : forall n, od n -> ev (S n)
  with od : nat -> Prop :=
  | odS : forall n, ev n -> od (S n)
  | odax : od ax.
  Definition u1 := evS.
  Definition u2 := ev0.
  Print Assumptions u1.
  Print Assumptions u2.
  Print Assumptions od.
  Print Assumptions odS.
  Print Assumptions u1.
End DefaultFlags.

Module Unguarded.
  Unset Guard Checking.
  Fixpoint loop (n : nat) : nat := loop n.
  Set Guard Checking.
  Definition use_loop := loop 0.
  Definition use_loop2 := use_loop.
  Print Assumptions use_loop.
  Print Assumptions use_loop2.
End Unguarded.

Module Unpositive.
  Unset Positivity Checking.
  Inductive neg : Type := mk_neg : (neg -> nat) -> neg
  with neg2 : Type := mk_neg2 : neg -> neg2.
  Set Positivity Checking.
  Definition use_neg2 := mk_neg2.
  Print Assumptions use_neg2.
  Print Assumptions neg.
  Print Assumptions use_neg2.
End Unpositive.
