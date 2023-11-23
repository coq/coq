(* -*- coq-prog-args: ("-async-proofs" "on" "-noinit"); -*- *)

Declare ML Module "coq-core.plugins.ltacX_common".
Declare ML Module "coq-core.plugins.ltac".

Set Default Proof Mode "Classic".

Goal Prop.
  idtac.
Abort.
