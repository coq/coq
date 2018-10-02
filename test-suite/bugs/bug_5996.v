Goal Type.
  let c := constr:(prod nat nat) in
  let c' := (eval pattern nat in c) in
  let c' := lazymatch c' with ?f _ => f end in
  let c'' := lazymatch c' with fun x : Set => ?f => constr:(forall x : Type, f) end in
  let _ := type of c'' in
  exact c''.
Defined.
