(* -*- mode: coq; coq-prog-args: ("-vos") -*- *)

Section foo.
  Context {H:True}.
  Theorem test1 : True.
  Proof.
    (* this gets printed with -vos because there's no annotation (either [Set
    Default Proof Using ...] or an explicit [Proof using ...]) *)
    idtac "without using".
    exact I.
  Qed.
End foo.
