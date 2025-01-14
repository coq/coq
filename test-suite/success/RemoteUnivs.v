

Goal Type * Type.
Proof.
  split.
  par: exact Type.
Qed.

Goal Type.
Proof.
  exact Type.
Qed.

(* (* rocqide test, note the delegated proofs seem to get an empty dirpath?
      or I got confused because I had lemma foo in file foo
 *)
Definition U := Type.

Lemma foo : U.
Proof.
  exact Type.
Qed.


Lemma foo1 : Type.
Proof.
  exact (U:Type).
Qed.

Print foo.
*)
