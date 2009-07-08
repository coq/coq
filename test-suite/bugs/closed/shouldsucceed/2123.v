(* About the detection of non-dependent metas by the refine tactic *)

(* The following is a simplification of bug #2123 *)

Parameter fset : nat -> Set.
Parameter widen : forall (n : nat) (s : fset n), { x : fset (S n) | s=s }.
Goal forall i, fset (S i).
intro.
refine (proj1_sig (widen i _)).


