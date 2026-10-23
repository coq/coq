(* Regression probe: a weak-head reduction must not normalize under a lambda. *)
Definition whnf_lambda :=
  Eval vm_compute_whnf in (fun _ : unit => 1 + 2).

Goal True.
Proof.
  let got := (eval unfold whnf_lambda in whnf_lambda) in
  let expected := constr:((fun _ : unit => 1 + 2)) in
  tryif constr_eq got expected
  then exact I
  else fail 0 "vm_compute_whnf normalized below the lambda:" got.
Qed.
