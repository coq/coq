(* About scoping of pattern variables in strict/non-strict mode *)

Ltac eta_red := change (fun a => ?f0 a) with f0.
Goal forall T1 T2 (f : T1 -> T2), (fun x => f x) = f.
intros.
eta_red.
Abort.
