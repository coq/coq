Goal True.
  set(a := 0).
  set(b := a).
  unfold a in b.
  clear a.
  Eval vm_compute in  b.
  trivial.
Qed.
