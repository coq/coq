Module Ex0.

Record S : Type := Pack { sort :> Type }.

Canonical SSet := Pack Set.

Check Set : S.
(* Error: Anomaly "Unable to handle arbitrary u+k <= v constraints." *)

End Ex0.

Module Ex1.

Record type : Type := Pack { sort :> nat -> Type }.

Definition set := fun _ : nat => Set.

Canonical inst := Pack set.

Set Printing All.
Set Printing Universes.

Check set : type.
(* Error: Anomaly "Unable to handle arbitrary u+k <= v constraints." *)

End Ex1.
