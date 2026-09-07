(* Confusion of kername translation of dot module separators and name underscores. *)
Module A. Module B. Definition x := true. End B. End A.
Module A_B. Definition x := false. End A_B.

Lemma via_vm : orb A.B.x A_B.x = true.
Proof. vm_compute; reflexivity. Qed.

Lemma via_native : orb A.B.x A_B.x = false.
Proof.
native_compute.
Fail reflexivity.
Abort.

(* Another similar example with underscore at the word boundary *)
Module X_. Definition foo := true. End X_.
Module X. Definition _foo := false. End X.

Lemma via_vm' : orb X_.foo X._foo = true.
Proof. vm_compute; reflexivity. Qed.

Lemma via_native' : orb X_.foo X._foo = false.
Proof.
native_compute.
Fail reflexivity.
Abort.
