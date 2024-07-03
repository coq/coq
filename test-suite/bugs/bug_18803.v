(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Symbol raise : forall A, A.

Rewrite Rule raise_rew :=
| match raise (unit = unit) as i in _ = t return t with eq_refl => ?t end => ?t.
