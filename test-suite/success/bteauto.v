
Class A := { foo : nat }.

Instance A_1 : A | 2 := { foo := 42 }.
Instance A_0 : A | 1 := { foo := 0 }.
Lemma aeq (a : A) : foo = foo.
  reflexivity.
Qed.

Goal exists n, n = 42.
  eexists.
  eapply eq_trans.
  evar (a : A). subst a.
  refine (@aeq ?a).
  Unshelve. all:cycle 1.
  typeclasses eauto.
  Fail reflexivity.
  Undo 2.
  Set Typeclasses Debug.
  (* Without multiple successes it fails *)
  Fail all:((once typeclasses eauto) + reflexivity).
  (* Does backtrack if other goals fail *)
  all:((typeclasses eauto) + reflexivity).
Qed.

Hint Extern 0 (_ = _) => reflexivity : typeclass_instances.

Goal exists n, n = 42.
  eexists.
  eapply eq_trans.
  evar (a : A). subst a.
  refine (@aeq ?a).
  Unshelve. all:cycle 1.
  typeclasses eauto.
  Fail reflexivity.
  Undo 2.
  Set Typeclasses Debug.
  (* Does backtrack between individual goals *)
  all:(typeclasses eauto).
Qed.
