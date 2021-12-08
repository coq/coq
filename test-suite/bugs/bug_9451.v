Goal False.
cut True.
assert False.
evar (x : True).
let v := open_constr:(_) in idtac. all: exfalso; clear.
Optimize Proof.
(* Error: Anomaly "grounding a non evar-free term" *)
Abort All.
