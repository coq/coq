(* Test maximal implicit arguments in the presence of let-ins *)
Definition foo (x := 1) {y : nat} (H : y = y) : True := I.
Definition bar {y : nat} (x := 1) (H : y = y) : True := I.
Check bar (eq_refl 1).
Check foo (eq_refl 1). 
