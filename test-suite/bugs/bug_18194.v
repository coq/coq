Require Import Corelib.Program.Tactics.

Program Definition a := Eval cbv zeta in (fun (a : True) => (?[A] : nat),
  let r :=
    let b := I in match tt with tt => b end
  in
  ?A@{a := r},
  fun (a : True) => (eq_refl : ?A = _)).

Next Obligation.
  destruct a; exact 0.
Defined.
(* This used to fail with the message:
File "test-suite/bugs/bug_18194.v", line 12, characters 0-8:
Error:
Unbound reference: In environment
anonymous' : unit
The reference 3 is free.
*)
