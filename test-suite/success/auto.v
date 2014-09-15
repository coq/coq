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
  eauto. 
Qed.

(* Test implicit arguments in "using" clause *)

Goal forall n:nat, nat * nat.
auto using (pair O).
Undo.
eauto using (pair O).
Qed.

Create HintDb test discriminated.

Parameter foo : forall x, x = x + 0.
Hint Resolve foo : test.

Variable C : nat -> Type -> Prop.

Variable c_inst : C 0 nat.

Hint Resolve c_inst : test.

Hint Mode C - + : test.
Hint Resolve c_inst : test2.
Hint Mode C + + : test2.

Goal exists n, C n nat.
Proof.
  eexists. Fail progress debug eauto with test2. 
  progress eauto with test.
Qed.
