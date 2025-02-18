Set Debug "all".
Set Universe Polymorphism.
Set Allow StrictProp.
Set Polymorphic Inductive Cumulativity.
Set Primitive Projections.
Record Iso@{s s'|u u'|} (a : Type@{s|u}) (b : Type@{s'|u'}) := { fwd : a -> b ; bwd : b -> a }.
Inductive sEmpty : SProp := .
Definition iso_sEmpty : Iso sEmpty sEmpty := {| fwd := fun x => x ; bwd := fun x => x |}.
#[local] Unset Universe Polymorphism.
Module Type Foo.
  Parameter bar : Type.
  Parameter baz : Iso bar bar.
End Foo.
Unset Universe Checking.
Module M <: Foo.
  Definition bar : Type := sEmpty.
  Definition baz : Iso bar bar.
  Proof. exact (iso_sEmpty : Iso@{SProp SProp|_ _} bar bar). Defined.
  (* The term "iso_sEmpty : Iso bar bar" has type
"Iso@{SProp SProp | IsomorphismChecker.Original.39
IsomorphismChecker.Original.40} bar bar"
while it is expected to have type
"Iso@{Type Type | bar.u0 bar.u0} bar bar". *)
Definition baz_default : Iso bar bar.
Proof. lazy. exact (iso_sEmpty : Iso@{SProp SProp|_ _} bar bar). Defined.
Definition baz_vm : Iso bar bar.
Proof. vm_compute. exact (iso_sEmpty : Iso@{SProp SProp|_ _} bar bar). Defined.
Definition baz_native : Iso bar bar.
Proof. native_compute. exact (iso_sEmpty : Iso@{SProp SProp|_ _} bar bar). Defined.
End M.


Set Allow StrictProp.
Set Universe Checking.
Polymorphic Record foo@{s|u|} (x : Type@{s|u}) := {}.
Module Type A. Axiom A : Type. Axiom B : foo A. End A.
Unset Universe Checking.
Set Printing Universes.
Module B <: A. Axiom A : SProp. Axiom B : foo A. End B.
(* Signature components for field B do not match: expected type
"foo@{Type | A.A.u0} IsomorphismChecker.bug_interface_04.B.A"
but found type
"foo@{SProp | IsomorphismChecker.bug_interface_04.72}
IsomorphismChecker.bug_interface_04.B.A". *)
