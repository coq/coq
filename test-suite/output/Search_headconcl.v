(* Some tests of the Search command *)

Search headconcl: le.				(* app nodes *)
Search headconcl: bool. 				(* no apps *)
Search headconcl: (@eq nat).			(* complex pattern *)

Definition newdef := fun x:nat => x = x.

Goal forall n:nat, newdef n -> False.
  intros n h.
  Search headconcl: newdef.             (* search hypothesis *)
Abort.


Goal forall n (P:nat -> Prop), P n -> False.
  intros n P h.
  Search headconcl: P.                  (* search hypothesis also for patterns *)
Abort.
