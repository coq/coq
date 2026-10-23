From Corelib Require Import PrimInt63 PrimArray PrimFloat PrimString.
Require Import Setoid.

(* Assert the actual syntax returned by an [Eval] reduction, rather than merely
   asserting that the command did not raise an unrelated error. *)
Ltac check_body name expected :=
  let got := (eval unfold name in name) in
  let want := constr:(expected) in
  tryif constr_eq got want
  then idtac
  else fail 0 "unexpected reduction result:" got "<>" want.

Definition no_stuck_closed := Eval vm_compute_no_stuck in 1 + 2.
Goal True.
Proof. check_body no_stuck_closed 3. exact I. Qed.

Definition whnf_closed := Eval vm_compute_whnf in 1 + 2.
Goal True.
Proof. check_body whnf_closed 3. exact I. Qed.

Parameter n : nat.
Parameter b : bool.
Parameter opaque : nat -> nat.

(* Exercise each blocked VM-stack shape below the root. *)
Fail Eval vm_compute_no_stuck in Some (Nat.add n 1).
Fail Eval vm_compute_no_stuck in Some (if b then 1 else 2).
Fail Eval vm_compute_no_stuck in (fun x => (Nat.add x 1, tt)).

(* A failure must not poison later VM evaluations or shared compilation data. *)
Definition after_failure := Eval vm_compute_no_stuck in opaque (1 + 2).
Goal True.
Proof. check_body after_failure (opaque 3). exact I. Qed.

(* The root-only policy accepts the same selected stuck forms below a value. *)
Eval vm_compute_whnf in Some (Nat.add n 1).
Eval vm_compute_whnf in Some (if b then 1 else 2).

(* Probe primitive arity and universe-argument accounting. *)
Open Scope uint63_scope.
Parameter i : PrimInt63.int.
Eval vm_compute_whnf in @PrimInt63.add.
Eval vm_compute_whnf in PrimInt63.add 1.
Fail Eval vm_compute_whnf in PrimInt63.add i 1.
Fail Eval vm_compute_no_stuck in (fun x : PrimInt63.int => PrimInt63.add x 1).
Close Scope uint63_scope.

Open Scope array_scope.
Parameter A : Type.
Parameter a : array A.
Parameter functions : array (nat -> nat).
Eval vm_compute_whnf in @PrimArray.get.
Eval vm_compute_whnf in (fun T => @PrimArray.get T).
Fail Eval vm_compute_whnf in @PrimArray.get A a 0.
(* The fully applied stuck primitive remains detectable when over-applied. *)
Fail Eval vm_compute_no_stuck in functions.[0] 1.
Close Scope array_scope.

Fail Eval vm_compute_no_stuck in
  (fun x : float => PrimFloat.add x x).
Fail Eval vm_compute_no_stuck in
  (fun s : PrimString.string => PrimString.length s).

(* Exercise the only tactic/conversion path which accepts arbitrary named
   reduction expressions. *)
Goal 1 + 2 = 3.
Proof.
  rewrite_strat (eval vm_compute_no_stuck).
  reflexivity.
Qed.

Goal 1 + 2 = 3.
Proof.
  rewrite_strat (eval vm_compute_whnf).
  reflexivity.
Qed.
