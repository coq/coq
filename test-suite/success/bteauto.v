
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

Fail Timeout 1 Check prf.

Hint Mode SomeProp + + : typeclass_instances.
Check prf.
Check (fun H : SomeProp plus => _ : SomeProp (flip plus)).































(** Iterative deepening / breadth-first search *)

Module IterativeDeepening.

  Class A.
  Class B.
  Class C.

  Instance: B -> A | 0.
  Instance: C -> A | 0.
  Instance: C -> B -> A | 0.
  Instance: A -> A | 0.
  
  Goal C -> A.
    intros.
    Set Typeclasses Debug.
    Fail Timeout 1 typeclasses eauto.
    Set Typeclasses Iterative Deepening.
    Fail typeclasses eauto 1.
    typeclasses eauto 2.
    Undo.
    Unset Typeclasses Iterative Deepening.
    Fail Timeout 1 typeclasses eauto.
    Set Typeclasses Iterative Deepening.
    Typeclasses eauto := debug 3.
    typeclasses eauto.
  Qed.

End IterativeDeepening.
