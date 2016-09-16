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

(* This was failing in 8.6, because of ?a:nat being wrongly duplicated *)

Goal (forall a : nat, a = 0 -> True) -> True.
intros F.
unshelve (eapply (F _);clear F).
2:reflexivity.
Qed.

Axioms A B : Prop.
Goal A /\ B -> exists a : A, B.
  clear; intros; evar (a:A); exists a.
  revert a.
  unshelve_evar ?a.
  unshelve_goals a. all:cycle 1. apply (proj1 H).
  Undo.
  shelve. instantiate (1:=ltac:(refine (proj1 ?[a']))).
  simple refine (let pf : A /\ B := ?[pf] in _); cycle 1.
  intro a.
  unify a (proj1 ?pf).
  unify (proj1 ?pf) a.
  Fail all: [ > unify ?pf ?a' | ]; [ | ].
  Fail all: [ > unify ?a' ?pf | ]; [ | ].
Abort.
