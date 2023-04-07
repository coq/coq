Require Import Ltac2.Ltac2.

Ltac2 rec fact n :=
  if Int.le n 1 then 1
  else Int.add (fact (Int.sub n 1)) (fact (Int.sub n 2)).

Ltac2 test val := List.init 50 (fun _ => val()).

Fail Timeout 1 Ltac2 Eval test (fun () => fact 25).

Time #[precompute] Ltac2 val := fact 25.
(* 0.5s *)

Timeout 1 Ltac2 Eval test (fun () => val).
