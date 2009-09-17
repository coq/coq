
Goal forall a b c : nat,  a = b -> b = c -> forall d, a+d=c+d.
intros.

(* "compatibility" mode: specializing a global name
   means a kind of generalize *)

specialize trans_equal. intros _.
specialize trans_equal with (1:=H)(2:=H0). intros _.
specialize trans_equal with (x:=a)(y:=b)(z:=c). intros _.
specialize trans_equal with (1:=H)(z:=c). intros _.
specialize trans_equal with nat a b c. intros _.
specialize (@trans_equal nat). intros _.
specialize (@trans_equal _ a b c). intros _.
specialize (trans_equal (x:=a)). intros _.
specialize (trans_equal (x:=a)(y:=b)). intros _.
specialize (trans_equal H H0). intros _.
specialize (trans_equal H0 (z:=b)). intros _.

(* local "in place" specialization *)
assert (Eq:=trans_equal).

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
specialize trans_equal with (1:=Eq).  (* mal typé !! *)

(* 3) *)
specialize trans_equal with _ a b c. intros _.
(* Anomaly: Evar ?88 was not declared. Please report. *)
*)

Abort.