Axioms A B : Type -> Type.
Axiom f : A nat -> B Type.

Definition A' := A nat.
Definition f' : A' -> B Type := f.
Coercion f' : A' >-> B.
Check (_ : A nat) : A'.
Fail Check (_ : A nat) : B Type. (* The term "?11:A nat" has type "A nat" while it is expected to have type "B Type". *)
Check ((_ : A nat) : A') : B Type. (* ((?11:A nat):A'):B Type *)

Fail Identity Coercion f'_id : A >-> A'. (* Error: in build_id_coercion: A must be a transparent constant. *)
Identity Coercion f'_id : A' >-> A.

Fail Check (_ : A nat) : B Type. (* The term "?11:A nat" has type "A nat" while it is expected to have type "B Type". *)

Coercion f : A >-> B. (* Warning: f does not respect the uniform inheritance condition *)

Check (_ : A nat) : B Type. (* Anomaly: apply_coercion_args. Please report. *)
