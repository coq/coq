(* -*- mode: coq; coq-prog-args: ("-vos") -*- *)

Section foo.
  Context {H:True}.
  Set Default Proof Using "Type".
  Theorem test2 : True.
  Proof.
    (* BUG: this gets run when compiling with -vos *)
    fail "proof with default using".
    exact I.
  Qed.

  Theorem test3 : True.
  Proof using Type.
    (* this isn't run with -vos *)
    fail "using".
    exact I.
  Qed.
End foo.
