(* This used to refer to b instead of z sometimes between 8.4 and 8.5beta3 *)
Goal True.
Fail let T := constr:((fun a b : nat => a+b) 1 1) in
  lazymatch T with
  | (fun x z => ?y) 1 1
    => pose ((fun x _ => y) 1 1)
  end.
Abort.

(* This should not raise a warning (see #4317) *)
Goal True.
assert (H:= eq_refl ((fun x => x) 1)).
let HT := type of H in
lazymatch goal with
| H1 : HT |- _ => idtac
end.
Abort.

(* Check printing of the "var" argument "Hx" *)
Ltac m H := idtac H; exact H.
Goal True.
let a:=constr:(let Hx := 0 in ltac:(m Hx)) in idtac.
