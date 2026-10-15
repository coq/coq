Require Import Corelib.Force TestSuite.vm_force_defs.

Ltac syn_refl := lazymatch goal with |- ?t = ?t => exact eq_refl end.
Notation VM t := (ltac:(let x := eval vm_compute in t in exact x)) (only parsing).
Notation BVM t := (ltac:(let x := eval vm_compute_blocking in t in exact x)) (only parsing).

Goal VM (__block nat (1 + 1)) = __block nat 2.
Proof. syn_refl. Qed.
Goal VM vm_saved_alias = __block nat 2.
Proof. syn_refl. Qed.
Goal VM vm_saved_capture = __block nat 3.
Proof. syn_refl. Qed.
Goal VM (__run _ _ vm_saved_capture (fun x => x)) = 3.
Proof. syn_refl. Qed.
Goal VM (@Blocked_ind nat (fun _ => nat) (fun x => S x) vm_saved_block) = 3.
Proof. syn_refl. Qed.
Goal VM ((@Blocked_ind nat (fun _ => nat)) (fun x => x) vm_saved_block) = 2.
Proof. syn_refl. Qed.

Axiom stuck : Blocked nat.
Goal VM (__run nat nat stuck (fun _ => 0)) = __run nat nat stuck (fun _ => 0).
Proof. syn_refl. Qed.
Goal VM (__run nat (nat -> nat) stuck (fun _ x => x) 1) =
  (__run nat (nat -> nat) stuck (fun _ x => x) 1).
Proof. syn_refl. Qed.
Goal VM (@Blocked_ind nat (fun _ => nat) (fun x => x) stuck) =
  @Blocked_ind nat (fun _ => nat) (fun x => x) stuck.
Proof. syn_refl. Qed.
Goal VM (__block nat (__unblock stuck)) =
  __block nat (__run nat nat stuck (fun x => x)).
Proof. syn_refl. Qed.

Goal VM (__block _ (fun n : nat => __unblock (__block _ (eq_refl n)))) =
  __block _ (fun n : nat => eq_refl n).
Proof. syn_refl. Qed.
Goal VM (__run _ _ (__block _ (fun n : nat => let m := n in
  __unblock (__block _ (eq_refl m)))) (fun f => f) 3) = eq_refl 3.
Proof. syn_refl. Qed.
Goal VM (vm_poly_block nat 3) = __block nat 3.
Proof. syn_refl. Qed.
Goal VM (vm_section_block nat 3) = __block nat 3.
Proof. syn_refl. Qed.
Goal VM (vm_poly_capture nat (__block nat 3)) = __block _ (fun _ : nat => 3).
Proof. syn_refl. Qed.

Inductive sunit : SProp := sitt.
Eval vm_compute in (__block sunit sitt).
Eval vm_compute in (__block sunit (__unblock (__block sunit sitt))).
Eval vm_compute in (fun (A : Type) (x : A) => __block A x).
Eval vm_compute in (vm_quality_block sunit sitt).
Eval vm_compute in (vm_quality_block True I).

Goal forall n : nat, n = n.
Proof.
  intro n.
  let b := eval vm_compute in (__block _ (eq_refl n)) in
  let expected := constr:(__block _ (eq_refl n)) in
  constr_eq b expected.
  reflexivity.
Qed.
Goal exists n : nat, n = 0.
Proof.
  evar (x : nat).
  let b := eval vm_compute in (__block nat x) in
  let expected := eval lazy in (__block nat x) in
  constr_eq b expected.
  let y := eval lazy in x in unify y 0.
  exists 0; reflexivity.
Qed.

(* This client sees original syntax even after another client forces the
   same imported constant, and vice versa. *)
Goal BVM vm_saved_alias = __block nat (1 + 1).
Proof. syn_refl. Qed.
Goal BVM (__block nat ((fun x : nat => x) (1 + 1))) =
  __block nat ((fun x : nat => x) (1 + 1)).
Proof. syn_refl. Qed.
Goal BVM (__block nat (1 + __unblock (__block nat (2 + 2)))) =
  __block nat (1 + (2 + 2)).
Proof. syn_refl. Qed.
Goal BVM (__run _ _ vm_saved_nested (fun x => x)) = __block nat (1 + 1).
Proof. syn_refl. Qed.
Goal BVM (__block nat (__run nat nat vm_saved_block (fun x => x))) =
  __block nat (__run nat nat vm_saved_block (fun x => x)).
Proof. syn_refl. Qed.
Goal BVM (__run _ _ vm_saved_alias (fun x => x)) = 2.
Proof. syn_refl. Qed.
Goal BVM (__block _ (fun n : nat => __unblock (__block _ (eq_refl n)))) =
  __block _ (fun n : nat => eq_refl n).
Proof. syn_refl. Qed.
Goal VM vm_saved_alias = __block nat 2.
Proof. syn_refl. Qed.
Goal VM vm_saved_nested = __block _ (__block nat 2).
Proof. syn_refl. Qed.

(* VM casts must not erase the hidden-entry layout checked by the kernel. *)
Definition one_capture := __block nat (__unblock stuck).
Definition two_captures := __block nat (let _ := __unblock stuck in __unblock stuck).
Fail Check (eq_refl one_capture <: one_capture = two_captures).
Check (eq_refl vm_saved_block <: vm_saved_alias = vm_saved_block).
Check (eq_refl 3 <: __run _ _ vm_saved_capture (fun x => x) = 3).

Module Type Input.
  Parameter n : nat.
End Input.
Module Make (I : Input).
  Definition b := __block nat (I.n + 1).
End Make.
Module Input2.
  Definition n := 2.
End Input2.
Module Output := Make Input2.
Goal VM Output.b = __block nat 3.
Proof. syn_refl. Qed.
Goal BVM Output.b = __block nat (Input2.n + 1).
Proof. syn_refl. Qed.

Goal BVM (1 + 1) = 2.
Proof. syn_refl. Qed.
Goal BVM (__run nat nat stuck (fun _ => 0)) = __run nat nat stuck (fun _ => 0).
Proof. syn_refl. Qed.

Definition vm_blocking_eval := Eval vm_compute_blocking in vm_saved_alias.
Goal vm_blocking_eval = __block nat (1 + 1).
Proof. unfold vm_blocking_eval; syn_refl. Qed.

Declare Reduction vm_blocking_alias := vm_compute_blocking.
Definition vm_blocking_alias_eval := Eval vm_blocking_alias in vm_saved_alias.
Goal vm_blocking_alias_eval = __block nat (1 + 1).
Proof. unfold vm_blocking_alias_eval; syn_refl. Qed.

(* Tactics use the same explicit strategy, including contexts and occurrences. *)
Definition vm_blocking_fun (_ : nat) := vm_saved_alias.
Goal vm_saved_alias = __block nat (1 + 1).
Proof.
  vm_compute_blocking.
  lazymatch goal with |- ?g =>
    let expected := constr:(__block nat (1 + 1) = __block nat (1 + 1)) in
    constr_eq g expected
  end.
  syn_refl.
Qed.
Goal vm_blocking_fun 0 = vm_blocking_fun 0.
Proof.
  vm_compute_blocking vm_blocking_fun at 1.
  lazymatch goal with |- ?g =>
    let expected := constr:(__block nat (1 + 1) = vm_blocking_fun 0) in
    constr_eq g expected
  end.
  reflexivity.
Qed.
Goal vm_blocking_fun 0 = vm_blocking_fun 0 -> True.
Proof.
  intro H.
  vm_compute_blocking vm_blocking_fun in H at 1.
  let t := type of H in
  let expected := constr:(__block nat (1 + 1) = vm_blocking_fun 0) in
  constr_eq t expected.
  exact I.
Qed.
