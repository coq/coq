(* Not supported but check at least that it does not raise an anomaly *)

Inductive Fin{n : nat} : Set :=
| F1{i : nat}{e : n = S i}
| FS{i : nat}(f : @ Fin i){e : n = S i}.

Fail Scheme Equality for Fin.
