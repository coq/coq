Require Import Coq.Program.Program.

Variable A : Set.

Inductive vector : nat -> Type := vnil : vector 0 | vcons : A -> forall n, vector n -> vector (S n).

Goal forall n, forall v : vector (S n), vector n.
Proof.
  intros n H.
  dependent induction H.
  inversion H0 ; subst.
  assumption.
Save.

Require Import ProofIrrelevance.

Goal forall n, forall v : vector (S n), exists v' : vector n, exists a : A, v = vcons a n v'.
Proof.
  intros n H.
  dependent induction H generalizing n.
  inversion H0 ; subst.
  rewrite (UIP_refl _ _ H0).
  simpl.
  exists H ; exists a.
  reflexivity.
Save.

(* Extraction Unnamed_thm. *)

Inductive type : Type :=
| base : type
| arrow : type -> type -> type.

Inductive ctx : Type :=
| empty : ctx
| snoc : ctx -> type -> ctx.

Inductive term : ctx -> type -> Type :=
| ax : forall G tau, term (snoc G tau) tau
| weak : forall G tau, term G tau -> forall tau', term (snoc G tau') tau
| abs : forall G tau tau', term (snoc G tau) tau' -> term G (arrow tau tau').

Fixpoint app (G D : ctx) : ctx :=
  match D with
    | empty => G
    | snoc D' x => snoc (app G D') x
  end.

Lemma weakening : forall G D tau, term (app G D) tau -> forall tau', term (app (snoc G tau') D) tau.
Proof with simpl in * ; auto.
  intros G D tau H.
  dependent induction H generalizing G D.

  destruct D...
    subst.
    apply weak ; apply ax.

    inversion H ; subst.
    apply ax.
    
  destruct D...
    subst.
    do 2 apply weak.
    assumption.

    apply weak.
    apply IHterm.
    inversion H0 ; subst ; reflexivity.

  cut(term (snoc (app G0 D) tau'0) (arrow tau tau') -> term (app (snoc G0 tau'0) D) (arrow tau tau')).
  intros.
  apply H0.
  apply weak.
  apply abs.
  assumption.

  intros.
Admitted.
