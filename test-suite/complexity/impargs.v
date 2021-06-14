(* Expected time < 1.00s *)

Fixpoint fib n :=
  match n with
  | O => 1
  | 1 => 1
  | S (S n as m) => fib n + fib m
  end.

(* In ored to compute implicit arguments the system has to whd this
   term. In call by name it takes a lot of time, in call by need it is
   instantaneous. *)
Definition statement k :=
  (fun v => match v + v + v + v + v with 0 => True | _ => forall x, x + 1 = x end)
  ((fun x => x - x) (fib k)).

Set Implicit Arguments.
Timeout 3 Time Axiom test : statement 20.
