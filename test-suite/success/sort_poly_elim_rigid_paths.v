Sort s s' s''.

Constraint s -> s'.
Constraint s' -> s''.

Polymorphic Axiom ad@{s0;u} : forall A : Univ@{s0;u}, A.
Polymorphic Definition t@{s0 s1;u v|s0 -> s1} (A : Univ@{s0;u}) (B : Univ@{s1;v}) : A := ad A.

(* This should succeed even though [s -> s''] is not declared *)
Check t@{s s'';Set Set}.

(* This should fail though as we don't have [s'' -> s'] or [s'' -> s] declared. *)
Fail Check t@{s'' s';Set Set}.
Fail Check t@{s'' s;Set Set}.
Fail Definition withelim@{|s'' -> s'} := tt.

(* But if we do this, both should work. *)
Constraint s'' -> s.
Check t@{s'' s';Set Set}.
Check t@{s'' s;Set Set}.
Definition withelim@{|s'' -> s'} := tt.
