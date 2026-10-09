Require Import Corelib.Force TestSuite.vm_force_defs Ltac2.Ltac2.

Ltac2 assert_same (actual : constr) (expected : constr) :=
  Control.assert_true (Constr.equal actual expected).

(* Both strategies can evaluate the same cached constant in either order. *)
Ltac2 Eval
  let full := eval vm_compute in vm_saved_alias in
  assert_same full '(__block nat 2);
  let blocked := eval vm_compute_blocking in vm_saved_alias in
  assert_same blocked '(__block nat (1 + 1));
  let full := Std.eval_vm None 'vm_saved_alias in
  assert_same full '(__block nat 2);
  let blocked := Std.eval_vm_blocking None 'vm_saved_alias in
  assert_same blocked '(__block nat (1 + 1)).

Ltac2 Eval
  let blocked := Std.eval (Std.Red.vm_blocking None) 'vm_saved_nested in
  assert_same blocked '(__block _ (__block nat (1 + 1)));
  let full := eval vm_compute in vm_saved_nested in
  assert_same full '(__block _ (__block nat 2)).

Ltac2 Eval
  let blocked := eval vm_compute_blocking in
    (__block nat (1 + __unblock (__block nat (2 + 2)))) in
  assert_same blocked '(__block nat (1 + (2 + 2)));
  let forced := eval vm_compute_blocking in
    (__run nat nat vm_saved_alias (fun x => x)) in
  assert_same forced '2.

Goal vm_saved_alias = __block nat (1 + 1).
Proof.
  vm_compute_blocking.
  assert_same (Control.goal ()) '(__block nat (1 + 1) = __block nat (1 + 1)).
  reflexivity.
Qed.

Definition vm_blocking_fun (_ : nat) := vm_saved_alias.

Goal vm_blocking_fun 0 = vm_blocking_fun 0.
Proof.
  vm_compute_blocking vm_blocking_fun at 1.
  assert_same (Control.goal ()) '(__block nat (1 + 1) = vm_blocking_fun 0).
  reflexivity.
Qed.

Goal vm_blocking_fun 0 = vm_blocking_fun 0 -> True.
Proof.
  intros H.
  vm_compute_blocking vm_blocking_fun in H at 1.
  assert_same (Constr.type (Control.hyp @H)) '(__block nat (1 + 1) = vm_blocking_fun 0).
  constructor.
Qed.
