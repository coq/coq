

Fixpoint fib n :=
  match n with
  | 0 => 1
  | S k =>
      match k with
      | 0 => 1
      | S p => fib k + fib p
      end
  end.

Fixpoint div2 n :=
  match n with
  | 0 | 1 => 0
  | S (S k) => S (div2 k)
  end.

(* example from the haskell profiling doc:
   costs are mostly in [fib] (for us actually in addition because unary integers)
   but we can tell that it's more the fib in [f] than the one in [g] *)

Definition f n := fib n.
Definition g n := fib (div2 n).

Definition main n := (f n, g n).

Set Debug "lazy".

Eval lazy in main 15.
