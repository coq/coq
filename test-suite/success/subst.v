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
