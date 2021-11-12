(* -*- mode: coq; coq-prog-args: ("-vio") -*- *)
Module M.
  Fail Definition foo := nonexistent.
End M.
