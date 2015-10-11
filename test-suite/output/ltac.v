(* This used to refer to b instead of z sometimes between 8.4 and 8.5beta3 *)
Goal True.
Fail let T := constr:((fun a b : nat => a+b) 1 1) in
  lazymatch T with
  | (fun x z => ?y) 1 1
    => pose ((fun x _ => y) 1 1)
  end.
Abort.
