(* Before loading Program, check non-anomaly on missing library Program *)

Fail Program Definition f n (e:n=n): {n|n=0} := match n,e with 0, refl => 0 | _, _ => 0 end.

(* Then we test Program properly speaking *)

Require Import Arith Program.
Require Import ZArith Zwf.

Set Implicit Arguments.
(* Set Printing All. *)
Print sigT_rect.
Obligation Tactic := program_simplify ; auto with *.
About MR.

Program Fixpoint merge (n m : nat) {measure (n + m) (lt)} : nat :=
  match n with
    | 0 => 0
    | S n' => merge n' m
  end.

Print merge.


Print Z.lt.
Print Zwf.

Local Open Scope Z_scope.

Program Fixpoint Zwfrec (n m : Z) {measure (n + m) (Zwf 0)} : Z :=
  match n ?= m with
    | Lt => Zwfrec n (Z.pred m)
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
Proof. intros. unfold merge at 1. unfold merge_func. 
  unfold_sub merge (merge n m).
  simpl. destruct n ; reflexivity. 
Qed.

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

Program Fixpoint check_n'  (n : nat) (m : {m:nat | m = n}) (p : nat) (q:{q : nat | q = p})
  {measure (p - n) p} : nat :=
  _.
