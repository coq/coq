(* -*- mode: coq; coq-prog-args: ("-vos") -*- *)
Section S.
  Fail Definition foo := nonexistent.
End S.
