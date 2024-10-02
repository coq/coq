(* -*- mode: coq; coq-prog-args: ("-vos") -*- *)

Set Default Proof Using "Type".

Section foo.
  Context (A:Type).
  #[sealed]
  Definition x : option A.
    (* this can get printed with -vos since without "Proof." there's no Proof
    using, even with a default annotation. *)
    idtac "creating x without [Proof.]".
    exact None.
  Qed.
End foo.
