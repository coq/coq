(* Before loading Program, check non-anomaly on missing library Program *)

Fail Program Definition f n (e:n=n): {n|n=0} := match n,e with 0, refl => 0 | _, _ => 0 end.

(* Then we test Program properly speaking *)

From Stdlib Require Import Arith Program.
From Stdlib Require Import ZArith Zwf.

Set Implicit Arguments.
(* Set Printing All. *)
Print sigT_rect.
Obligation Tactic := program_simplify ; auto with *.
About MR.

Program Fixpoint merge (n m : nat) {measure (n + m) lt} : nat :=
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

From Stdlib Require Import Arith.
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

From Stdlib Require Import Lia Setoid.

Next Obligation.
  intros ; simpl in *. apply H.
  simpl in * ; lia.
Qed.

Next Obligation. simpl in *; intros.
  revert e ; clear_subset_proofs. intros.
  case (le_gt_dec p i) ; intro. simpl in *. assert(p = i) by lia. subst.
  revert e ; clear_subset_proofs ; tauto.

  apply H. simpl. lia.
Qed.

Program Fixpoint check_n'  (n : nat) (m : {m:nat | m = n}) (p : nat) (q:{q : nat | q = p})
  {measure (p - n)} : nat :=
  _.
Module FurtherArguments.

Program Fixpoint zero (n : nat) {measure n} : nat -> nat :=
  match n with
    | 0 => fun _ => 0
    | S n' => zero n'
  end.

Program Fixpoint f n {B} (b:B) {measure n} : forall {A}, A -> A * B :=
  match n with
  | 0 => fun A a => (a, b)
  | S n => fun A a => f n b a
  end.

End FurtherArguments.

Module Notations.

Reserved Notation "[ x ]".
Program Fixpoint zero (n : nat) {measure n} : nat -> nat :=
  match n with
    | 0 => fun _ => 0
    | S n' => [ n' ]
  end

where "[ n ]" := (zero n).

Check eq_refl : ([ 0 ] 0) = 0.

Reserved Notation "[[ x | y ]]".
Program Fixpoint zero' (n : nat) {measure n} : nat -> nat :=
  match n with
    | 0 => fun _ => 0
    | S n' => fun a => [[ n' | a ]]
  end

where "[[ n | p ]]" := (zero' n p).

Check eq_refl : [[ 0 | 0 ]] = 0.

End Notations.
