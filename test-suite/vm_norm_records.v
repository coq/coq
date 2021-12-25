Set Primitive Projections.

(** Variant of VM conversion that exercises the reification part of the VM *)
Ltac norm := match goal with [ |- ?P ] => let Q := eval vm_compute in P in change Q end.

Module T.

Record prod (A : Type) (B : A -> Type) := pair { fst : A; snd : B fst }.

Arguments fst {_ _}.
Arguments snd {_ _}.

Goal forall (p : prod nat (fun n => n = 0)), fst p = 0.
Proof.
intros p.
norm.
apply (snd p).
Qed.

End T.

Module M.

CoInductive foo := Foo {
  foo0 : foo;
  foo1 : bar;
}
with bar := Bar {
  bar0 : foo;
  bar1 : bar;
}.

CoFixpoint f : foo := Foo f g
with g : bar := Bar f g.

Goal f.(foo0).(foo0) = g.(bar0).
Proof.
norm.
match goal with [ |- ?t = ?t ] => idtac end.
reflexivity.
Qed.

Goal g.(bar1).(bar0).(foo1) = g.
Proof.
norm.
match goal with [ |- ?t = ?t ] => idtac end.
reflexivity.
Qed.

End M.

Module N.

Inductive foo := Foo {
  foo0 : option foo;
  foo1 : list bar;
}
with bar := Bar {
  bar0 : option bar;
  bar1 : list foo;
}.

Definition f_0 := Foo None nil.
Definition g_0 := Bar None nil.

Definition f := Foo (Some f_0) (cons g_0 nil).

Goal f.(foo1) = cons g_0 nil.
Proof.
norm.
match goal with [ |- ?t = ?t ] => idtac end.
reflexivity.
Qed.

End N.
