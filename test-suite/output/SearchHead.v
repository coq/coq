(* Some tests of the Search command *)

SearchHead le.				(* app nodes *)
SearchHead bool. 				(* no apps *)
SearchHead (@eq nat).			(* complex pattern *)

Definition newdef := fun x:nat => x = x.

Goal forall n:nat, newdef n -> False.
  intros n h.
  SearchHead newdef.             (* search hypothesis *)
Abort.


Goal forall n (P:nat -> Prop), P n -> False.
  intros n P h.
  SearchHead P.                  (* search hypothesis also for patterns *)
Abort.

