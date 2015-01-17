Set Universe Polymorphism.

Polymorphic Definition id {A : Type} (a : A) := a.

Eval vm_compute in id 1.

Polymorphic Inductive ind (A : Type) := cons : A -> ind A.

Eval vm_compute in ind unit.

Check ind unit.

Eval vm_compute in ind unit.

Definition bar := Eval vm_compute in ind unit.
Definition bar' := Eval vm_compute in id (cons _ tt).

Definition bar'' := Eval native_compute in id 1.
Definition bar''' := Eval native_compute in id (cons _ tt).

Definition barty := Eval native_compute in id (cons _ Set).

Definition one := @id.

Monomorphic Definition sec := one.

Eval native_compute in sec.
Definition sec' := Eval native_compute in sec.
Eval vm_compute in sec.
Definition sec'' := Eval vm_compute in sec.


