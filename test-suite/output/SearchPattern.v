(* Some tests of the SearchPattern command *)

(* Simple, random tests *)
SearchPattern bool.
SearchPattern nat.
SearchPattern le.

(* With some hypothesis *)
SearchPattern (nat -> nat).
SearchPattern (?n * ?m + ?n = ?n * S ?m).

(* Non-linearity *)
SearchPattern (_ ?X ?X).

(* Non-linearity with hypothesis *)
SearchPattern (forall (x:?A) (y:?B), _ ?A ?B).

(* No delta-reduction *)
SearchPattern (Exc _).

Definition newdef := fun x:nat => x.

Goal forall n:nat, n <> newdef n -> False.
  intros n h.
  SearchPattern ( _ <> newdef _).          (* search hypothesis *)
  SearchPattern ( n <> newdef _).          (* search hypothesis *)
Abort.

Goal forall n (P:nat -> Prop), P n -> ~P n -> False.
  intros n P h h'.
  SearchPattern (P _).      (* search hypothesis also for patterns *)
  Search (~P n).          (* search hypothesis also for patterns *)
  Search (P _) -"h'".       (* search hypothesis also for patterns *)
  Search (P _) -not.       (* search hypothesis also for patterns *)

Abort.
