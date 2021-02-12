Goal True.
evar (p : bool).
unify ?p true.
let v := eval vm_compute in (orb p false) in
match v with true => idtac end.
assert (orb p false = true).
vm_compute.
match goal with |- true = _ => idtac end.
easy.
easy.
Qed.
