(* -*- coq-prog-args: ("-async-proofs" "on" "-noinit"); -*- *)

Declare ML Module "rocq-runtime.plugins.ltac".

Set Default Proof Mode "Classic".

Goal Prop.
  idtac.
Abort.
