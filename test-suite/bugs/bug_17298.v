Goal True.
let c := open_constr:(_) in
let _ := open_constr:(c : nat) in
pose (x:=c);
pose (y := c).

(* evars remain, do not use the kernel *)
Check (eq_refl : x = y).

(* evars remain, since we don't recheck with the kernel this is accepted *)
Check (ltac:(exact_no_check (@eq_refl nat 0)) : x = y).

(* no evars, check that the kernel got the normalized env *)
Check (eq_refl : x = 0).

Fail Check (ltac:(let _ := open_constr:(eq_refl : x = 0) in
                  exact_no_check (@eq_refl nat 1)) : x = 0).
Abort.
