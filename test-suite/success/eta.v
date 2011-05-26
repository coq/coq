(* Kernel test (head term is a constant) *)
Check (fun a : S = S => a : S = fun x => S x).

(* Kernel test (head term is a variable) *)
Check (fun (f:nat->nat) (a : f = f) => a : f = fun x => f x).

(* Test type inference  (head term is syntactically rigid) *)
Check (fun (a : list = list) => a : list = fun A => _ A).

(* Test type inference (head term is a variable) *)
(* This one is still to be done...
Check (fun (f:nat->nat) (a : f = f) => a : f = fun x => _ x).
*)

(* Test tactic unification *)
Goal (forall f:nat->nat, (fun x => f x) = (fun x => f x)) -> S = S.
intro H; apply H.
Qed.

