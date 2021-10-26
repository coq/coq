(* Assumed to be compiled with -R test-from T *)
From T.B Require C.

Definition c := C.c.
Lemma foo : c = false.
Proof.
reflexivity.
Qed.
