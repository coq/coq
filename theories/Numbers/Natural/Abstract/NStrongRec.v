(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(** This file defined the strong (course-of-value, well-founded) recursion
and proves its properties *)

Require Export NSub.

Ltac f_equiv' := repeat (repeat f_equiv; try intros ? ? ?; auto).

Module NStrongRecProp (Import N : NAxiomsRecSig').
Include NSubProp N.

Section StrongRecursion.

Variable A : Type.
Variable Aeq : relation A.
Variable Aeq_equiv : Equivalence Aeq.

(** [strong_rec] allows defining a recursive function [phi] given by
    an equation [phi(n) = F(phi)(n)] where recursive calls to [phi]
    in [F] are made on strictly lower numbers than [n].

    For [strong_rec a F n]:
    - Parameter [a:A] is a default value used internally, it has no
      effect on the final result.
    - Parameter [F:(N->A)->N->A] is the step function:
      [F f n] should return [phi(n)] when [f] is a function
      that coincide with [phi] for numbers strictly less than [n].
*)

Definition strong_rec (a : A) (f : (N.t -> A) -> N.t -> A) (n : N.t) : A :=
 recursion (fun _ => a) (fun _ => f) (S n) n.

(** For convenience, we use in proofs an intermediate definition
    between [recursion] and [strong_rec]. *)

Definition strong_rec0 (a : A) (f : (N.t -> A) -> N.t -> A) : N.t -> N.t -> A :=
 recursion (fun _ => a) (fun _ => f).

Lemma strong_rec_alt : forall a f n,
 strong_rec a f n = strong_rec0 a f (S n) n.
Proof.
reflexivity.
Qed.

Instance strong_rec0_wd :
 Proper (Aeq ==> ((N.eq ==> Aeq) ==> N.eq ==> Aeq) ==> N.eq ==> N.eq ==> Aeq)
  strong_rec0.
Proof.
unfold strong_rec0; f_equiv'.
Qed.

Instance strong_rec_wd :
 Proper (Aeq ==> ((N.eq ==> Aeq) ==> N.eq ==> Aeq) ==> N.eq ==> Aeq) strong_rec.
Proof.
intros a a' Eaa' f f' Eff' n n' Enn'.
rewrite !strong_rec_alt; f_equiv'.
Qed.

Section FixPoint.

Variable f : (N.t -> A) -> N.t -> A.
Variable f_wd : Proper ((N.eq==>Aeq)==>N.eq==>Aeq) f.

Lemma strong_rec0_0 : forall a m,
 (strong_rec0 a f 0 m) = a.
Proof.
intros. unfold strong_rec0. rewrite recursion_0; auto.
Qed.

Lemma strong_rec0_succ : forall a n m,
 Aeq (strong_rec0 a f (S n) m) (f (strong_rec0 a f n) m).
Proof.
intros. unfold strong_rec0.
f_equiv.
rewrite recursion_succ; f_equiv'.
Qed.

Lemma strong_rec_0 : forall a,
 Aeq (strong_rec a f 0) (f (fun _ => a) 0).
Proof.
intros. rewrite strong_rec_alt, strong_rec0_succ; f_equiv'.
rewrite strong_rec0_0. reflexivity.
Qed.

(* We need an assumption saying that for every n, the step function (f h n)
calls h only on the segment [0 ... n - 1]. This means that if h1 and h2
coincide on values < n, then (f h1 n) coincides with (f h2 n) *)

Hypothesis step_good :
  forall (n : N.t) (h1 h2 : N.t -> A),
    (forall m : N.t, m < n -> Aeq (h1 m) (h2 m)) -> Aeq (f h1 n) (f h2 n).

Lemma strong_rec0_more_steps : forall a k n m, m < n ->
 Aeq (strong_rec0 a f n m) (strong_rec0 a f (n+k) m).
Proof.
 intros a k n. pattern n.
 apply induction; clear n.

 intros n n' Hn; setoid_rewrite Hn; auto with *.

 intros m Hm. destruct (nlt_0_r _ Hm).

 intros n IH m Hm.
 rewrite lt_succ_r in Hm.
 rewrite add_succ_l.
 rewrite 2 strong_rec0_succ.
 apply step_good.
 intros m' Hm'.
 apply IH.
 apply lt_le_trans with m; auto.
Qed.

Lemma strong_rec0_fixpoint : forall (a : A) (n : N.t),
 Aeq (strong_rec0 a f (S n) n) (f (fun n => strong_rec0 a f (S n) n) n).
Proof.
intros.
rewrite strong_rec0_succ.
apply step_good.
intros m Hm.
symmetry.
setoid_replace n with (S m + (n - S m)).
apply strong_rec0_more_steps.
apply lt_succ_diag_r.
rewrite add_comm.
symmetry.
apply sub_add.
rewrite le_succ_l; auto.
Qed.

Theorem strong_rec_fixpoint : forall (a : A) (n : N.t),
 Aeq (strong_rec a f n) (f (strong_rec a f) n).
Proof.
intros.
transitivity (f (fun n => strong_rec0 a f (S n) n) n).
rewrite strong_rec_alt.
apply strong_rec0_fixpoint.
f_equiv.
intros x x' Hx; rewrite strong_rec_alt, Hx; auto with *.
Qed.

(** NB: without the [step_good] hypothesis, we have proved that
    [strong_rec a f 0] is [f (fun _ => a) 0]. Now we can prove
    that the first argument of [f] is arbitrary in this case...
*)

Theorem strong_rec_0_any : forall (a : A)(any : N.t->A),
 Aeq (strong_rec a f 0) (f any 0).
Proof.
intros.
rewrite strong_rec_fixpoint.
apply step_good.
intros m Hm. destruct (nlt_0_r _ Hm).
Qed.

(** ... and that first argument of [strong_rec] is always arbitrary. *)

Lemma strong_rec_any_fst_arg : forall a a' n,
 Aeq (strong_rec a f n) (strong_rec a' f n).
Proof.
intros a a' n.
generalize (le_refl n).
set (k:=n) at -2. clearbody k. revert k. pattern n.
apply induction; clear n.
(* compat *)
intros n n' Hn. setoid_rewrite Hn; auto with *.
(* 0 *)
intros k Hk. rewrite le_0_r in Hk.
rewrite Hk, strong_rec_0. symmetry. apply strong_rec_0_any.
(* S *)
intros n IH k Hk.
rewrite 2 strong_rec_fixpoint.
apply step_good.
intros m Hm.
apply IH.
rewrite succ_le_mono.
apply le_trans with k; auto.
rewrite le_succ_l; auto.
Qed.

End FixPoint.
End StrongRecursion.

Arguments strong_rec [A] a f n.

End NStrongRecProp.

