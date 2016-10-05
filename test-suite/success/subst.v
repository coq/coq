(* Test various subtleties of the "subst" tactics *)

(* Should proceed from left to right (see #4222) *)
Goal forall x y, x = y -> x = 3 -> y = 2 -> x = y.
intros.
subst.
change (3 = 2) in H1.
change (3 = 3).
Abort.

(* Should work with "x = y" and "x = t" equations (see #4214, failed in 8.4) *)
Goal forall x y, x = y -> x = 3 -> x = y.
intros.
subst.
change (3 = 3).
Abort.

(* Should substitute cycles once, until a recursive equation is obtained *)
(* (failed in 8.4) *)
Goal forall x y, x = S y -> y = S x -> x = y.
intros.
subst.
change (y = S (S y)) in H0.
change (S y = y).
Abort.

(* A bug revealed by OCaml 4.03 warnings *)
(* fixes in 4e3d464 and 89ec88f for v8.5, 4e3d4646 and 89ec88f1e for v8.6 *)
Goal forall y, let x:=0 in y=x -> y=y.
intros * H;
(* This worked as expected *)
subst.
Fail clear H.
Abort.

Goal forall y, let x:=0 in x=y -> y=y.
intros * H;
(* Before the fix, this unfolded x instead of 
   substituting y and erasing H *)
subst.
Fail clear H.
Abort.
