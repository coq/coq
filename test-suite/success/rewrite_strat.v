Require Import Setoid.


Parameter X : Set.

Parameter f : X -> X.
Parameter g : X -> X -> X.
Parameter h : nat -> X -> X.

Parameter lem0 : forall x, f (f x) = f x.
Parameter lem1 : forall x, g x x = f x.
Parameter lem2 : forall n x, h (S n) x = g (h n x) (h n x).
Parameter lem3 : forall x, h 0 x = x.

#[export] Hint Rewrite lem0 lem1 lem2 lem3 : rew.

Goal forall x, h 10 x = f x.
Proof.
  intros.
  Time autorewrite with rew. (* 0.586 *)
  reflexivity.
Time Qed. (* 0.53 *)

Goal forall x, h 6 x = f x.
intros.
  Time rewrite_strat topdown lem2.
  Time rewrite_strat topdown lem1.
  Time rewrite_strat topdown lem0.
  Time rewrite_strat topdown lem3.
  reflexivity.
Undo 5.
  Time rewrite_strat topdown (choice lem2 lem1).
  Time rewrite_strat topdown (choice lem0 lem3).
  reflexivity.
Undo 3.
  Time rewrite_strat (topdown (choice lem2 lem1); topdown (choice lem0 lem3)).
  reflexivity.
Undo 2.
  Time rewrite_strat (topdown (choice (choice lem2 lem1) (choice lem0 lem3))).
  reflexivity.
Undo 2.
  Time rewrite_strat (topdown (choice lem2 (choice lem1 (choice lem0 lem3)))).
  reflexivity.
Undo 2.
  Time rewrite_strat (topdown (choice lem2 lem1 lem0 lem3)).
  reflexivity.
Undo 2.
  Time rewrite_strat fix f := (choice lem2 lem1 lem0 lem3 (progress subterms f) ; try f).
  reflexivity.
Qed.

Goal forall x, h 10 x = f x.
Proof.
  intros.
  Time rewrite_strat topdown (hints rew). (* 0.38 *)
  reflexivity.
Time Qed. (* 0.06 s *)

(* Set Printing All. *)
(* Set Printing Depth 100000. *)

Tactic Notation "my_rewrite_strat" constr(x) := rewrite_strat topdown x.
Tactic Notation "my_rewrite_strat2" uconstr(x) := rewrite_strat topdown x.
Goal (forall x, S x = 0) -> 1=0.
intro H.
my_rewrite_strat H.
Undo.
my_rewrite_strat2 H.
Abort.

Module StratMatches.
  Lemma add_0_r x : x + 0 = x.
  Admitted.

  Goal forall x : nat, x + (x + 0) = x + x.
  Proof.
    Fail rewrite_strat (bottomup (matches (x + 0) ; add_0_r)).
    rewrite_strat (bottomup (matches (_ + 0) ; add_0_r)).
    reflexivity.
  Qed.

  Goal forall x : nat, x + (x + 0) = x + x.
  Proof.
    intros x.
    rewrite_strat (bottomup (matches (x + 0) ; add_0_r)).
    reflexivity.
  Qed.

  (* Heavy computation if unfolded at any point during unification *)
  Definition foo (n : nat) :=
    Nat.pow 2 n.

  Goal foo (200 + 200) = foo 400.
  Proof.
    rewrite_strat (bottomup (matches (_ + _); eval cbn)).
    reflexivity.
  Qed.

  Goal foo (200 + 200) = foo (399 + 1).
  Proof.
    rewrite_strat (bottomup (matches (_ + _); eval cbn)).
    reflexivity.
  Qed.

  Import Decimal.

  Lemma heavy : foo (2000 + 2000) = foo (40 * 100).
  Proof.
    (* Fail Timeout 1 cbn. *)
    (* 1.5sec *)
    Time rewrite_strat (bottomup (choice (matches (_ + _)) (matches (_ * _)); eval cbn)).
    Undo.
    (* ~30x faster: 0.05s *)
    Time rewrite_strat (bottomup (choice (matches (_ + _)) (matches (_ * _)); eval vm_compute)).
    reflexivity.
  Defined.

  (* A more complex situation where FO unification is not tried *)
  Definition bar n (k : nat) := foo n.

  Lemma heavier : foo (200 + 2000 + 1800) = bar (400 * 10) 10.
  Proof.
    (* exact_no_check (@eq_refl nat 40000). *)
    (* Fail Timeout 1 Qed. *)
    (* Undo. Undo. *)
    (* Strategy 200 [Nat.add]. *)
    (* Strategy -300 [Nat.pow foo]. *)
    (* (* Fail Timeout 1 reflexivity. *) *)
    (* (* Fail Timeout 1 cbn. *) *)
    (* (* Untractable *) *)
    (* (* Fail Timeout 1 rewrite_strat (bottomup (choice (matches (_ + _)) (matches (_ * _)); eval cbn)). *) *)
    (* (* 0.5s *) *)
    Time rewrite_strat (bottomup (choice (matches (_ + _)) (matches (_ * _)); eval vm_compute)).
    unfold bar; reflexivity.
    (* Immmediate *)
  Defined.

End StratMatches.
Import Decimal Nat.

Module StratTactic.

  Ltac is_closed_add t :=
    match t with
    | Nat.add _ _ => idtac
    end.

  Ltac reduce_fo_ind_value :=
    match goal with
    | [ |- ?R ?lhs ?rhs ] =>
        let ty := type of lhs in
        match ty with
        | nat =>
            is_closed_add lhs;
            (* idtac "match"; *)
          let rhs' := eval cbv in lhs in
            (* instantiate is using right-to-left order! *)
            instantiate (2 := @eq ty);
            instantiate (1 := rhs');
            exact_no_check (@eq_refl ty rhs')
        end
    end.

  (* Heavy computation if unfolded at any point during unification *)
  Definition foo (n : nat) :=
    Nat.pow 2 n.

  Ltac reduce_fo_ind :=
    rewrite_strat (fix s := choice (tactic reduce_fo_ind_value) (subterm s)).

  Variant rewrite {A : Type} (lhs : A) : Prop :=
    | success : forall (R : A -> A -> Prop) (rhs : A) (prf : R lhs rhs), rewrite lhs
    | fail : rewrite lhs
    | identity : rewrite lhs.

  Lemma heavy : foo (200 + 200) = foo 400.
  Proof.
    Time reduce_fo_ind.
    reflexivity.
  Time Qed.

  Lemma binders (b : bool) : forall x, (2 + x) = S (S x).
  Proof.
    reduce_fo_ind.
    match goal with
    | |- forall x, S (S x) = S (S x) => idtac
    end.
    trivial.
  Qed.

End StratTactic.

Module RewriteLet.
  Import Nat.

  (* In a "deep" context *)

  Axiom f : nat -> nat.

  Goal forall x : nat, f (let x0 := x + 1 in x0 + x0) = f (S (S (x + x))).
  Proof.
    intros x.
    rewrite_strat (topdown (choice (<- plus_n_Sm) (<- plus_n_O))).
    reflexivity.
  Qed.

  (* In a toplevel context, requiring to mediate between [eq] and [impl] / [flip impl] *)
  Goal forall x : nat, let x0 := x + 1 in x0 = x0.
  Proof.
    intros x.
    now rewrite_strat (topdown (choice (<- plus_n_Sm) (<- plus_n_O))).
  Qed.

  Goal forall x : nat, (let x0 := x + 1 in x0 = x0) -> S x = S x.
  Proof.
    intros x H.
    rewrite_strat (topdown (choice (<- plus_n_Sm) (<- plus_n_O))) in H.
    exact H.
  Qed.

End RewriteLet.
