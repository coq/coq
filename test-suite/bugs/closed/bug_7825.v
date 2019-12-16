Record T (x : nat) := { t : x = x }.

Set Debug  Refine.

Goal exists x, T x.
  refine (ex_intro _ _ _).
  Show Existentials.
  simple refine {| t := _ |}.
  reflexivity.
  Unshelve. exact 0.
Qed.

(** Fine if the new evar is defined as the originally shelved evar:  we do nothing.
  In the other direction we promote the non-shelved new goal to a shelved one:
  shelved status has priority over goal status. *)

Goal forall a : nat,  exists x, T x.
   evar (x : nat). subst x. Show Existentials.
   intros a. simple refine (ex_intro ?[x0] _ _). shelve. simpl.
   (** Here ?x := ?x0 which is shelved, so ?x becomes shelved even if it would
   not be by default (refine ?x and _ produce non-shelved evars by default)*)
   simple refine (Build_T ?x _).
   reflexivity.
   Unshelve. exact 0.
Qed.
