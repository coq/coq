(* Wish #2154 by E. van der Weegen *)

(* auto was not using f_equal-style lemmas with metavariables occuring
   only in the type of an evar of the concl, but not directly in the
   concl itself *)

Parameters
  (F: Prop -> Prop)
  (G: forall T, (T -> Prop) -> Type)
  (L: forall A (P: A -> Prop), G A P -> forall x, F (P x))
  (Q: unit -> Prop).

Hint Resolve L.

Goal G unit Q -> F (Q tt).
  intro.
  auto.
Qed.

(* Test implicit arguments in "using" clause *)

Goal forall n:nat, nat * nat.
auto using (pair O).
Undo.
eauto using (pair O).
Qed.
