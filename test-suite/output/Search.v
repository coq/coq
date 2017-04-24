(* Some tests of the Search command *)

Search le.				(* app nodes *)
Search bool. 				(* no apps *)
Search (@eq nat).			(* complex pattern *)
Search (@eq _ _ true).
Search (@eq _ _ _) true -false.         (* andb_prop *)
Search (@eq _ _ _) true -false "prop" -"intro".  (* andb_prop *)
       
Definition newdef := fun x:nat => x.

Goal forall n:nat, n <> newdef n -> newdef n <> n -> False.
  cut False.
  intros _ n h h'.
  Search n.                             (* search hypothesis *)
  Search newdef.                        (* search hypothesis *)
  Search ( _ <> newdef _).              (* search hypothesis, pattern *)
  Search ( _ <> newdef _) -"h'".        (* search hypothesis, pattern *)

  1:Search newdef.
  2:Search newdef.

  Fail 3:Search newdef.
  Fail 1-2:Search newdef.
  Fail all:Search newdef.
Abort.

Goal forall n (P:nat -> Prop), P n -> ~P n -> False.
  intros n P h h'.
  Search P.                 (* search hypothesis also for patterns *)
  Search (P _).             (* search hypothesis also for patterns *)
  Search (P n).             (* search hypothesis also for patterns *)
  Search (P _) -"h'".       (* search hypothesis also for patterns *)
  Search (P _) -not.       (* search hypothesis also for patterns *)

Abort.

