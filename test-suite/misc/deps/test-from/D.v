(* Assumed to be compiled with -R test-from T *)
From T.A Require C.

Definition c := C.c.
Lemma foo : c = true.
Proof.
reflexivity.
Qed.
