Goal nat.
Proof.
let x := constr:(0) in
let y := uconstr:(ltac:(exact x)) in
refine (ltac:(exact y)).
(* The reference x was not found in the current environment. *)
Qed.
