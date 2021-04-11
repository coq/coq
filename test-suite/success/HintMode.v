Module Postponing.

Class In A T := { IsIn : A -> T -> Prop }.
Class Empty T := { empty : T }.
Class EmptyIn (A T : Type) `{In A T} `{Empty T} :=
 { isempty : forall x, IsIn x empty -> False }.

#[local] Hint Mode EmptyIn ! ! - - : typeclass_instances.
#[local] Hint Mode Empty ! : typeclass_instances.
#[local] Hint Mode In ! - : typeclass_instances.
Existing Class IsIn.
Goal forall A T `{In A T} `{Empty T} `{EmptyIn A T}, forall x : A, IsIn x empty -> False.
 Proof.
   intros.
   eapply @isempty. (* Second goal needs to be solved first, to un-stuck the first one
   (hence the Existing Class IsIn to allow finding the assumption of IsIn here)  *)
   all:typeclasses eauto.
Qed.

End Postponing.


Module HintModeDecl.

  Class Foo (A : Type) := foo : A.

  Instance: Foo nat := 0.
  Type foo.

  #[mode="+"]
  Class FooPlus (A : Type) := fooplus : A.
  Instance: FooPlus nat := 0.
  Fail Type fooplus.

  Set Typeclasses Default Mode "!".
  Class FooDefault (A : Type) := foodefault : A.
  Print HintDb typeclass_instances. (* mode ! *)

  Instance: FooDefault nat := 0.
  Fail Type foodefault.

  Instance default_list : FooDefault (list nat) := { foodefault := nil }.
  Type (foodefault : list _).
  Set Warnings "class-declaration-default-mode".

  Section Bla.
    Context (A : Type).
    #[mode="+"]
    Class FooSec (B : Type) := { bar : A -> B -> nat }.
  End Bla. (* In VSCoq the warning is not displayed as it is attached to an unknown stateid, but
    coqc displays it. If the warning is made an error it is properly reported *)
  Print HintDb typeclass_instances. (* Default mode = !, FooSec -> ! + *)

  Class Baz (A : Type).

End HintModeDecl.
