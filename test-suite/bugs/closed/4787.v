(* [Unset Bracketing Last Introduction Pattern] was not working *)

Unset Bracketing Last Introduction Pattern.

Goal forall T (x y : T * T), fst x = fst y /\ snd x = snd y -> x = y.
do 10 ((intros [] || intro); simpl); reflexivity.
Qed.


