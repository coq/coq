Require Import Corelib.Force.

Definition vm_saved_block : Blocked nat := __block nat (1 + 1).
Definition vm_saved_alias := vm_saved_block.
Definition vm_saved_capture : Blocked nat :=
  __block nat (1 + __unblock (__block nat (1 + 1))).
Definition vm_saved_nested : Blocked (Blocked nat) :=
  __block _ (__block nat (1 + 1)).

Polymorphic Definition vm_poly_block@{u} (A : Type@{u}) (x : A) : Blocked A :=
  __block A x.
Polymorphic Definition vm_poly_capture@{u} (A : Type@{u}) (b : Blocked A) :=
  __block _ (fun _ : A => __unblock b).
Polymorphic Definition vm_quality_block@{s;u} (A : Type@{s;u}) (x : A) :=
  __block@{s;u} A x.

Set Universe Polymorphism.
Section Captures.
  Variable A : Type.
  Variable x : A.
  Definition vm_section_block : Blocked A := __block A x.
End Captures.
