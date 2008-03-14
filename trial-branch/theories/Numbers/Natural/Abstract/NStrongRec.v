(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i i*)

(** This file defined the strong (course-of-value, well-founded) recursion
and proves its properties *)

Require Export NMinus.

Module NStrongRecPropFunct (Import NAxiomsMod : NAxiomsSig).
Module Export NMinusPropMod := NMinusPropFunct NAxiomsMod.
Open Local Scope NatScope.

Section StrongRecursion.

Variable A : Set.
Variable Aeq : relation A.

Notation Local "x ==A y" := (Aeq x y) (at level 70, no associativity).

Hypothesis Aeq_equiv : equiv A Aeq.

Add Relation A Aeq
 reflexivity proved by (proj1 Aeq_equiv)
 symmetry proved by (proj2 (proj2 Aeq_equiv))
 transitivity proved by (proj1 (proj2 Aeq_equiv))
as Aeq_rel.

Definition strong_rec (a : A) (f : N -> (N -> A) -> A) (n : N) : A :=
recursion
  (fun _ : N => a)
  (fun (m : N) (p : N -> A) (k : N) => f k p)
  (S n)
  n.

Theorem strong_rec_wd :
forall a a' : A, a ==A a' ->
  forall f f', fun2_eq Neq (fun_eq Neq Aeq) Aeq f f' ->
    forall n n', n == n' ->
      strong_rec a f n ==A strong_rec a' f' n'.
Proof.
intros a a' Eaa' f f' Eff' n n' Enn'.
(* First we prove that recursion (which is on type N -> A) returns
extensionally equal functions, and then we use the fact that n == n' *)
assert (H : fun_eq Neq Aeq
  (recursion
    (fun _ : N => a)
    (fun (m : N) (p : N -> A) (k : N) => f k p)
    (S n))
  (recursion
    (fun _ : N => a')
    (fun (m : N) (p : N -> A) (k : N) => f' k p)
    (S n'))).
apply recursion_wd with (Aeq := fun_eq Neq Aeq).
unfold fun_eq; now intros.
unfold fun2_eq. intros y y' Eyy' p p' Epp'. unfold fun_eq. auto.
now rewrite Enn'.
unfold strong_rec.
now apply H.
Qed.

(*Section FixPoint.

Variable a : A.
Variable f : N -> (N -> A) -> A.

Hypothesis f_wd : fun2_wd Neq (fun_eq Neq Aeq) Aeq f.

Let g (n : N) : A := strong_rec a f n.

Add Morphism g with signature Neq ==> Aeq as g_wd.
Proof.
intros n1 n2 H. unfold g. now apply strong_rec_wd.
Qed.

Theorem NtoA_eq_symm : symmetric (N -> A) (fun_eq Neq Aeq).
Proof.
apply fun_eq_symm.
exact (proj2 (proj2 NZeq_equiv)).
exact (proj2 (proj2 Aeq_equiv)).
Qed.

Theorem NtoA_eq_trans : transitive (N -> A) (fun_eq Neq Aeq).
Proof.
apply fun_eq_trans.
exact (proj1 NZeq_equiv).
exact (proj1 (proj2 NZeq_equiv)).
exact (proj1 (proj2 Aeq_equiv)).
Qed.

Add Relation (N -> A) (fun_eq Neq Aeq)
 symmetry proved by NtoA_eq_symm
 transitivity proved by NtoA_eq_trans
as NtoA_eq_rel.

Add Morphism f with signature Neq ==> (fun_eq Neq Aeq) ==> Aeq as f_morph.
Proof.
apply f_wd.
Qed.

(* We need an assumption saying that for every n, the step function (f n h)
calls h only on the segment [0 ... n - 1]. This means that if h1 and h2
coincide on values < n, then (f n h1) coincides with (f n h2) *)

Hypothesis step_good :
  forall (n : N) (h1 h2 : N -> A),
    (forall m : N, m < n -> Aeq (h1 m) (h2 m)) -> Aeq (f n h1) (f n h2).

(* Todo:
Theorem strong_rec_fixpoint : forall n : N, Aeq (g n) (f n g).
Proof.
apply induction.
unfold predicate_wd, fun_wd.
intros x y H. rewrite H. unfold fun_eq; apply g_wd.
reflexivity.
unfold g, strong_rec.
*)

End FixPoint.*)
End StrongRecursion.

Implicit Arguments strong_rec [A].

End NStrongRecPropFunct.

