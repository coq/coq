Axiom F : forall (b : bool), b = true ->
  forall (i : unit), i = i -> True.

Goal True.
Proof.
unshelve (refine (F _ _ _ _)).
+ exact true.
+ exact tt.
+ exact (@eq_refl bool true).
+ exact (@eq_refl unit tt).
Qed.


Axioms A B : Prop.
Goal A /\ B -> exists a : A, B.
  clear; intros; evar (a:A); exists a.
  revert a.
  unshelve_evar ?a.
  unshelve_goals a; cycle 1. apply (proj1 H).
  Undo.
  shelve. instantiate (1:=ltac:(refine (proj1 ?[a']))).
  simple refine (let pf : A /\ B := ?[pf] in _); cycle 1.
  intro a.
  unify a (proj1 ?pf).
  unify (proj1 ?pf) a.
  Fail all: [ > unify ?pf ?a' | ]; [ | ].
  Fail all: [ > unify ?a' ?pf | ]; [ | ].
