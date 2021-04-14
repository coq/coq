(* a file to check that vio-checking is not a noop *)

Lemma foo : Type.
Proof. match goal with |- ?G => exact G end. Qed.
