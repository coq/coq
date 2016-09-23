(* Checking let-in abstraction *)
Goal let x := Set in let y := x in True.
  intros x y.
  (* There used to have a too strict dependency test there *)
  set (s := Set) in (value of x).
