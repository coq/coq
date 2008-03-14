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

Require Import List.
Require Import Setoid.

(** An attempt to extend setoid rewrite to formulas with quantifiers *)

(* The following algorithm was explained to me by Bruno Barras.

In the future, we need to prove that some predicates are
well-defined w.r.t. a setoid relation, i.e., we need to prove theorems
of the form "forall x y, x == y -> (P x <-> P y)". The reason is that it
makes sense to do induction only on predicates P that satisfy this
property. Ideally, such goal should be proved by saying "intros x y H;
rewrite H; reflexivity".

Such predicates P may contain quantifiers besides setoid morphisms.
Unfortunately, the tactic "rewrite" (which in this case stands for
"setoid_rewrite") currently cannot handle universal quantifiers as well
as lambda abstractions, which are part of the existential quantifier
notation (recall that "exists x, P" stands for "ex (fun x => p)").

Therefore, to prove that P x <-> P y, we proceed as follows. Suppose
that P x is C[forall z, A[x,z]] where C is a context, i.e., a term with
a hole. We assume that the hole of C does not occur inside another
quantifier, i.e., that forall z, A[x,z] is a top-level quantifier in P.
The notation A[x,z] means that x and z occur freely in A. We prove that
forall z, A[x,z] <-> forall z, A[y,z]. To do this, we show that
forall z, A[x,z] <-> A[y,z]. After performing "intro z", this goal is
handled recursively, until no more quantifiers are left in A.

After we obtain the goal

H : x == y
H1 : forall z, A[x,z] <-> forall z, A[y,z]
=================================
C[forall z, A[x,z]] <-> C[forall z, A[y,z]]

we say "rewrite H1". The tactic setoid_rewrite can handle this because
"forall z" is a top-level quantifier. Repeating this for other
quantifier subformulas in P, we make them all identical in P x and P y.
After that, saying "rewrite H" solves the goal.

The job of deriving P x <-> P y from x == y is done by the tactic
qmorphism x y below. *)

Section Quantifiers.

Variable A : Set.

Theorem exists_morph : forall P1 P2 : A -> Prop,
  (forall x : A, P1 x <-> P2 x) -> (ex P1 <-> ex P2).
Proof.
(intros P1 P2 H; split; intro H1; destruct H1 as [x H1];
exists x); [now rewrite <- H | now rewrite H].
Qed.

Theorem forall_morph : forall P1 P2 : A -> Prop,
  (forall x : A, P1 x <-> P2 x) -> ((forall x : A, P1 x) <-> (forall x : A, P2 x)).
Proof.
(intros P1 P2 H; split; intros H1 x); [now apply -> H | now apply <- H].
Qed.

End Quantifiers.

(* replace x by y in t *)
Ltac repl x y t :=
match t with
| context C [x] => let t' := (context C [y]) in repl x y t'
| _ => t
end.

(* The tactic qiff x y H solves the goal P[x] <-> P[y] from H : E x y
where E is a registered setoid relation, P may contain quantifiers,
and x and y are arbitrary terms *)
Ltac qiff x y H :=
match goal with
| |- ?P <-> ?P => reflexivity
(* The clause above is needed because if the goal is trivial, i.e., x
and y do not occur in P, "setoid_replace x with y" below would produce
an error. *)
| |- context [ex ?P] =>
  lazymatch P with
  | context [x] =>
    let P' := repl x y P in
      setoid_replace (ex P) with (ex P') using relation iff;
      [qiff x y H | apply exists_morph; intro; qiff x y H]
  end
| |- context [forall z, @?P z] =>
  lazymatch P with
  | context [x] =>
    let P' := repl x y P in
      setoid_replace (forall z, P z) with (forall z, P' z) using relation iff;
      [qiff x y H | apply forall_morph; intro; qiff x y H]
  end
| _ => setoid_rewrite H; reflexivity
end.

Ltac qsetoid_rewrite H :=
lazymatch (type of H) with
| ?E ?t1 ?t2 =>
  lazymatch goal with
  | |- (fun x => @?G x) t1 =>
    let H1 := fresh in
    let H2 := fresh in
    let x1 := fresh "x" in
    let x2 := fresh "x" in
    set (x1 := t1); set (x2 := t2);
    assert (H1 : E x1 x2) by apply H;
    assert (H2 : (fun x => G x) x1 <-> (fun x => G x) x2) by qiff x1 x2 H1;
    unfold x1 in *; unfold x2 in *; apply <- H2;
    clear H1 H2 x1 x2
  | _ => pattern t1; qsetoid_rewrite H
  end
| _ => fail "The type of" H "does not have the form (E t1 t2)"
end.

Tactic Notation "qsetoid_rewrite" "<-" constr(H) :=
match goal with
| |- ?G =>
  let H1 := fresh in
    pose proof H as H1;
    symmetry in H1; (* symmetry unfolds the beta-redex in the goal (!), so we have to restore the goal *)
    change G;
    qsetoid_rewrite H1;
    clear H1
end.

Tactic Notation "qsetoid_replace" constr(t1) "with" constr(t2)
                "using" "relation" constr(E) :=
let H := fresh in
lazymatch goal with
| |- ?G =>
  cut (E t1 t2); [intro H; change G; qsetoid_rewrite H; clear H |]
end.

(* For testing *)

(*Parameter E : nat -> nat -> Prop.
Axiom eq_equiv : equiv nat E.

Add Relation nat E
 reflexivity proved by (proj1 eq_equiv)
 symmetry proved by (proj2 (proj2 eq_equiv))
 transitivity proved by (proj1 (proj2 eq_equiv))
as eq_rel.

Notation "x == y" := (E x y) (at level 70).

Parameter P : nat -> nat.
Add Morphism S with signature E ==> E as S_morph. Admitted.
Add Morphism P with signature E ==> E as P_morph. Admitted.
Add Morphism plus with signature E ==> E ==> E as plus_morph. Admitted.

Theorem Zplus_pred : forall n m : nat, P n + m == P (n + m).
Proof.
intros n m.
cut (forall n : nat, S (P n) == n). intro H.
pattern n at 2.
qsetoid_rewrite <- (H n).
Admitted.

Goal forall x, x == x + x ->
  (exists y, forall z, y == y + z -> exists u, x == u) /\ x == 0.
intros x H1. pattern x at 1.
qsetoid_rewrite H1. qsetoid_rewrite <- H1.
Admitted.*)

(* For the extension that deals with multiple equalities. The idea is
to give qiff a list of hypothesis instead of just one H. *)

(*Inductive EqList : Type :=
| eqnil : EqList
| eqcons : forall A : Prop, A -> EqList -> EqList.

Implicit Arguments eqcons [A].

Ltac ra L :=
lazymatch L with
| eqnil => reflexivity
| eqcons ?H ?T => rewrite H; ra T
end.

ra (eqcons H0 (eqcons H1 eqnil)).*)

