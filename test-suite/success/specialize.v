
Goal forall a b c : nat,  a = b -> b = c -> forall d, a+d=c+d.
intros.

(* "compatibility" mode: specializing a global name
   means a kind of generalize *)

specialize eq_trans. intros _.
specialize eq_trans with (1:=H)(2:=H0). intros _.
specialize eq_trans with (x:=a)(y:=b)(z:=c). intros _.
specialize eq_trans with (1:=H)(z:=c). intros _.
specialize eq_trans with nat a b c. intros _.
specialize (@eq_trans nat). intros _.
specialize (@eq_trans _ a b c). intros _.
specialize (eq_trans (x:=a)). intros _.
specialize (eq_trans (x:=a)(y:=b)). intros _.
specialize (eq_trans H H0). intros _.
specialize (eq_trans H0 (z:=b)). intros _.

(* local "in place" specialization *)
assert (Eq:=eq_trans).

specialize Eq.
specialize Eq with (1:=H)(2:=H0). Undo.
specialize Eq with (x:=a)(y:=b)(z:=c). Undo.
specialize Eq with (1:=H)(z:=c). Undo.
specialize Eq with nat a b c. Undo.
specialize (Eq nat). Undo.
specialize (Eq _ a b c). Undo.
(* no implicit argument for Eq, hence no (Eq (x:=a)) *)
specialize (Eq _ _ _ _ H H0). Undo.
specialize (Eq _ _ _ b H0). Undo.

(*
(** strange behavior to inspect more precisely *)

(* 1) proof aspect : let H:= ... in (fun H => ..) H
    presque ok... *)

(* 2) echoue moins lorsque zero premise de mangé *)
specialize eq_trans with (1:=Eq).  (* mal typé !! *)

(* 3) *)
specialize eq_trans with _ a b c. intros _.
(* Anomaly: Evar ?88 was not declared. Please report. *)
*)

Abort.