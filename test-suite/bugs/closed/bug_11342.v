(* -*- mode: coq; coq-prog-args: ("-vos") -*- *)

Section foo.
  Context {H:True}.
  Theorem test1 : True.
  Proof.
    (* this gets printed with -vos because there's no annotation *)
    idtac "without using".
    exact I.
  Qed.
End foo.

Section foo.
  Context {H:True}.
  Set Default Proof Using "Type".
  Theorem test2 : True.
  Proof.
    (* BUG: this gets printed when compiling with -vos *)
    fail "proof with default using".
    exact I.
  Qed.

  Theorem test3 : True.
  Proof using Type.
    (* this isn't printed with -vos *)
    fail "using".
    exact I.
  Qed.
End foo.
