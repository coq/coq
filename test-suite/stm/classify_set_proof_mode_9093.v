(* -*- coq-prog-args: ("-async-proofs" "on" "-noinit"); -*- *)

Declare ML Module "ltac_plugin:coq-core.plugins.ltac".

Set Default Proof Mode "Classic".

Goal Prop.
  idtac.
Abort.
