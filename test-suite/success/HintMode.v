Module Postponing.

Class In A T := { IsIn : A -> T -> Prop }.
Class Empty T := { empty : T }.
Class EmptyIn (A T : Type) `{In A T} `{Empty T} :=
 { isempty : forall x, IsIn x empty -> False }.

Hint Mode EmptyIn ! ! - - : typeclass_instances.
Hint Mode Empty ! : typeclass_instances.
Hint Mode In ! - : typeclass_instances.
Existing Class IsIn.
Goal forall A T `{In A T} `{Empty T} `{EmptyIn A T}, forall x : A, IsIn x empty -> False.
 Proof.
   intros.
   eapply @isempty. (* Second goal needs to be solved first, to un-stuck the first one
   (hence the Existing Class IsIn to allow finding the assumption of IsIn here)  *)
   all:typeclasses eauto.
Qed.

End Postponing.

Module BestEffort.

  Class A (T : Type).
  Global Hint Mode A + : typeclass_instances.
  Class B (T : Type).
  Global Hint Mode B + : typeclass_instances.

  Instance a_imp_b T : A T -> B T := {}.
  Instance anat : B nat := {}.
  Lemma b : B nat * A nat.
  Proof.
    Fail split; typeclasses eauto.
    Set Typeclasses Debug Verbosity 2.
    Fail split; solve [typeclasses eauto best_effort].
    (* Here typeclasses eauto best_effort, when run on the 2 goals at once,
       can solve the B goal which has a nat instance nd whose mode is +
       (this morally assumes that there is only one instance matching B nat)
    *)
    split; typeclasses eauto best_effort.
    admit.
  Admitted.

End BestEffort.
