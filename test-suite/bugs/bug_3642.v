Lemma foo (T : Type) : True.
evar (x : T).
Fail change ?x with ?x. (* Error: Ltac variable x is not bound to an identifier. It cannot be used in a binder. *)
Abort.
