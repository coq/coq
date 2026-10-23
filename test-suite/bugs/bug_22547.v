Notation "###" := true.  (* lonely notation *)
Notation "###" := 0 : nat_scope.

About S.
(* Arguments S x%_nat_scope *)

Check S ###.  (* ### in nat_scope *)
Check S ###%bool.  (* ### used to be the lonely notation *)
Check S ###%_bool.  (* ### used to be the lonely notation *)
(* before fix: Error: The term "###" has type "bool" while it is expected to have type "nat". *)
