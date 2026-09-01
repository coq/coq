Module MultipleFrozenModes.
  Class Foo (x y : nat).

  Global Instance foo_10_10 : Foo 10 10 := {}.

  Global Hint Mode Foo = - : typeclass_instances.

  Goal exists y, Foo 10 y.
  Proof. eexists. typeclasses eauto. Qed.

  Global Hint Mode Foo - = : typeclass_instances.

  (* Multiple mode declarations are alternatives: the newer mode must not
     prevent resolution under an older mode. *)
  Goal exists y, Foo 10 y.
  Proof. eexists. typeclasses eauto. Qed.

  (* Conversely, alternatives must not be merged into a more permissive mode:
     neither declared mode allows both evars to be instantiated. *)
  Goal exists x y, Foo x y.
  Proof. eexists; eexists. Fail typeclasses eauto. Abort.
End MultipleFrozenModes.

Module PermissiveAlternative.
  Class C (n : nat).

  Global Instance c_1 : C 1 := {}.

  Global Hint Mode C ! : typeclass_instances.
  Global Hint Mode C = : typeclass_instances.

  (* Although the newest mode freezes the evar, the older [!] mode permits
     resolution because the evar is not at the head of the argument. *)
  Goal exists n, C (S n).
  Proof. eexists. typeclasses eauto. Qed.
End PermissiveAlternative.

Module NonmatchingAlternative.
  Class C (n : nat).

  Global Instance c_0 : C 0 := {}.

  Global Hint Mode C + : typeclass_instances.
  Global Hint Mode C = : typeclass_instances.

  (* The [+] mode does not match an evar and must not make the matching [=]
     mode more permissive. *)
  Goal exists n, C n.
  Proof. eexists. Fail typeclasses eauto. Abort.
End NonmatchingAlternative.

Module StrictResolution.
  #[local] Set Typeclasses Strict Resolution.

  Class C (x y : nat).

  Global Instance c_0_1 : C 0 1 := {}.

  Global Hint Mode C = - : typeclass_instances.
  Global Hint Mode C - = : typeclass_instances.

  (* The second mode would permit the first evar to be instantiated, but Strict
     Resolution takes precedence over every matching mode alternative. *)
  Goal exists x, C x 1.
  Proof. eexists. Fail typeclasses eauto. Abort.

  Goal C 0 1.
  Proof. typeclasses eauto. Qed.
End StrictResolution.

Module ExternModes.
  Class C (n : nat).

  Global Instance c_0 : C 0 := {}.
  Global Hint Extern 0 (C _) => exact c_0 : typeclass_instances.

  Global Hint Mode C + : typeclass_instances.

  Goal exists n, C n.
  Proof. eexists. Fail typeclasses eauto. Abort.

  Global Hint Mode C = : typeclass_instances.

  (* A successful extern result is rejected if it instantiates an evar frozen
     by the matching mode.  Rejecting it also rolls back the assignment. *)
  Goal exists n, C n.
  Proof.
    eexists ?[n].
    Fail typeclasses eauto.
    instantiate (n := 1).
  Abort.
End ExternModes.

Module ExternAlternativeModes.
  Class C (x y : nat).

  Definition c_y1 (x : nat) : C x 1.
  Proof. constructor. Defined.
  Global Hint Extern 0 (C ?x _) => exact (c_y1 x) : typeclass_instances.

  Global Hint Mode C = - : typeclass_instances.
  Global Hint Mode C - = : typeclass_instances.

  (* The newer mode freezes [y], so its extern result is rejected.  Search must
     retry the extern under the older mode, which freezes [x] instead. *)
  Goal exists x y, C x y /\ x = 0 /\ y = 1.
  Proof.
    eexists ?[x], ?[y].
    split.
    - typeclasses eauto.
    - split; reflexivity.
  Qed.
End ExternAlternativeModes.

Module ExternGeneratedSubgoals.
  Class C (n : nat).
  Class D (n : nat).

  Definition c_of_d (n : nat) (_ : D n) : C n.
  Proof. constructor. Defined.
  Global Instance d_0 : D 0 := {}.
  Global Hint Extern 0 (C ?n) => eapply (c_of_d n) : typeclass_instances.
  Global Hint Mode C = : typeclass_instances.

  (* The extern itself leaves [n] undefined.  Its generated [D n] subgoal may
     instantiate [n], since modes constrain only the hint application. *)
  Goal exists n, C n.
  Proof. eexists. typeclasses eauto. Qed.
End ExternGeneratedSubgoals.

Module StrictExternException.
  #[local] Set Typeclasses Strict Resolution.

  Class C (n : nat).

  Definition c_0 : C 0.
  Proof. constructor. Defined.
  Global Hint Extern 0 (C _) => exact c_0 : typeclass_instances.

  (* Strict Resolution historically does not constrain Hint Extern. *)
  Goal exists n, C n.
  Proof. eexists. typeclasses eauto. Qed.
End StrictExternException.
