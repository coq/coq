(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Symbol t : unit.

Rewrite Rule t_rew :=
| match t with tt => @eq_refl ?A ?a end => @eq_refl ?A ?a.
