Require Import Arith Program.
Set Implicit Arguments.
(* Set Printing All. *)
Print sigT_rect.
Obligation Tactic := program_simplify ; auto with *.

Program Fixpoint merge (n m : nat) {measure (n + m) on lt} : nat :=
  match n with
    | 0 => 0
    | S n' => merge n' m
  end.

Print merge.

Require Import ZArith.


Print Zlt. 
Require Import Zwf.
Print Zwf.

Open Local Scope Z_scope.

Program Fixpoint Zwfrec (n m : Z) {measure (n + m) on (Zwf 0)} : Z :=
  match n ?= m with
    | Lt => Zwfrec n (Zpred m)
    | _ => 0
  end.

Next Obligation. 
  red. Admitted.

Close Scope Z_scope.

Program Fixpoint merge_wf (n m : nat) {wf lt m} : nat :=
  match n with
    | 0 => 0
    | S n' => merge n' m
  end.

Print merge_wf.

Program Fixpoint merge_one (n : nat) {measure n} : nat :=
  match n with
    | 0 => 0
    | S n' => merge_one n'
  end.

Print Hint well_founded.
Print merge_one. Eval cbv delta [merge_one] beta zeta in merge_one.

Import WfExtensionality.

Lemma merge_unfold n m : merge n m = 
  match n with
    | 0 => 0
    | S n' => merge n' m
  end.
Proof. intros. unfold_sub merge (merge n m). simpl. destruct n ; reflexivity. Qed.

Print merge.

Require Import Arith.
Unset Implicit Arguments.

Time Program Fixpoint check_n  (n : nat) (P : { i | i < n } -> bool) (p : nat)
  (H : forall (i : { i | i < n }), i < p -> P i = true)
  {measure (n - p)} : 
  Exc (forall (p : { i | i < n}), P p = true) :=
  match le_lt_dec n p with
  | left _ => value _
  | right cmp =>
      if dec (P p) then
        check_n n P (S p) _
      else
        error
  end.

Require Import Omega Setoid.

Next Obligation. 
  intros ; simpl in *. apply H. 
  simpl in * ; omega.
Qed.

Next Obligation. simpl in *; intros. 
  revert H0 ; clear_subset_proofs. intros. 
  case (le_gt_dec p i) ; intro. simpl in *. assert(p = i) by omega. subst. 
  revert H0 ; clear_subset_proofs ; tauto.

  apply H. simpl. omega.
Qed.

Print check_n.
Print sigT_rect.
Print check_n.

Program Fixpoint check_n'  (n : nat) (m : nat | m = n) (p : nat) (q : nat | q = p)
  {measure (p - n) p} : nat :=
  _.

Print Opaque Dependencies check_n.

