(* -*- mode: coq; coq-prog-args: ("-vio") -*- *)
Section S.
  Fail Definition foo := nonexistent.
End S.
