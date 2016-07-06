
Definition Foo {T}{a : T} : T := a.

Module A.

  Declare Implicit Tactic eauto.

  Goal forall A (x : A), A.
  intros.
  apply Foo. (* Check defined evars are normalized *)
  (*  Qed. *)
  Abort.

End A.

Module B.

  Definition Foo {T}{a : T} : T := a.

  Declare Implicit Tactic eassumption.

  Goal forall A (x : A), A.
  intros.
  apply Foo.
  (*  Qed. *)
  Abort.

End B.

Module C.

  Declare Implicit Tactic first [exact True|assumption].

  Goal forall (x : True), True.
  intros.
  apply (@Foo _ _).
  Qed.

End C.

Module D.

  Declare Implicit Tactic assumption.

  Goal forall A (x : A), A.
  intros.
  exact _.
  Qed.

End D.
