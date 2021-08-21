Goal True.
  lazymatch constr:(fun T (a : T) (b : T -> T) => b a) with
  | fun (x : ?T) => ?f
    => pose (match nat with
             | x => f
             end)
  end.
Check eq_refl : n = fun (a : nat) (b : nat -> nat) => b a.
Abort.

Goal True.
  lazymatch constr:(fun T (a : T) (b : T -> T) => b a) with
  | fun T => ?f
    => pose (match nat as T return _ with
             | T => f
             end)
  end.
Check eq_refl : n = fun (a : nat) (b : nat -> nat) => b a.
Abort.
