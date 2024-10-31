Axiom nth_error : list nat -> unit.
Axiom nth_error_value_length : forall (xs:list nat), nth_error xs = tt -> True.

Axiom type : Set.

Lemma foo (eta_ident_cps : forall {T : type -> Type} {t} (f : forall t', T t'), T t) : True.
Proof.
Fail apply nth_error_value_length in eta_ident_cps.
Abort.
