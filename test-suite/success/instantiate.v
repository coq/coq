(* Test régression bug #1041 *)

Goal Prop.

pose (P:= fun x y :Prop => y).
evar (Q: forall X Y,P X Y -> Prop) .

instantiate (1:= fun _ => _ ) in (Value of Q).
instantiate (1:= fun _ => _ ) in (Value of Q).
instantiate (1:= fun _ => _ ) in (Value of Q).
instantiate (1:= H) in (Value of Q).
