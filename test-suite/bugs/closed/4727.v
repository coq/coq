(* -*- coq-prog-args: ("-compat" "8.4") -*- *)
Goal forall (P : Set) (l : P) (P0 : Set) (w w0 : P0) (T : Type) (a : P * T) (o : P -> option P0),
    (forall (l1 l2 : P) (w1 : P0), o l1 = Some w1 -> o l2 = Some w1 -> l1 = l2) ->
    o l = Some w -> o (fst a) = Some w0 -> {w = w0} + {w <> w0} -> False.
Proof.
  clear; intros ???????? inj H0 H1 H2.
  destruct H2; intuition subst.
  eapply inj in H1; [ | eauto ].
  progress subst. (* should succeed, used to not succeed *)
Abort.
