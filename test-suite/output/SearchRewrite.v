(* Some tests of the SearchRewrite command *)

SearchRewrite (_+0). 			(* left *)
SearchRewrite (0+_). 			(* right *)

Definition newdef := fun x:nat => x.

Goal forall n:nat, n = newdef n -> False.
  intros n h.
  SearchRewrite (newdef _).
  SearchRewrite n.                (* use hypothesis for patterns *)
  SearchRewrite (newdef n).       (* use hypothesis for patterns *)
Abort.
