(* -*- mode: coq; coq-prog-args: ("-vos") -*- *)
Module M.
  Fail Definition foo := nonexistent.
End M.
