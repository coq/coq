Require Import Coq.Program.Program.
Set Implicit Arguments.
Unset Strict Implicit.

Variable A : Set.

Inductive vector : nat -> Type := vnil : vector 0 | vcons : A -> forall n, vector n -> vector (S n).

Goal forall n, forall v : vector (S n), vector n.
Proof.
  intros n H.
  dependent destruction H.
  assumption.
Save.

Require Import ProofIrrelevance.

Goal forall n, forall v : vector (S n), exists v' : vector n, exists a : A, v = vcons a v'.
Proof.
  intros n H.
  dependent destruction H.
  exists H ; exists a.
  reflexivity.
Save.

(* Extraction Unnamed_thm. *)

Inductive type : Type :=
| base : type
| arrow : type -> type -> type.

Notation " t --> t' " := (arrow t t') (at level 20, t' at next level).

Inductive ctx : Type :=
| empty : ctx
| snoc : ctx -> type -> ctx.

Notation " G , tau " := (snoc G tau) (at level 20, t at next level).

Fixpoint conc (G D : ctx) : ctx :=
  match D with
    | empty => G
    | snoc D' x => snoc (conc G D') x
  end.

Notation " G ; D " := (conc G D) (at level 20).

Inductive term : ctx -> type -> Type :=
| ax : forall G tau, term (G, tau) tau
| weak : forall G tau, 
  term G tau -> forall tau', term (G, tau') tau
| abs : forall G tau tau', 
  term (G , tau) tau' -> term G (tau --> tau')
| app : forall G tau tau', 
  term G (tau --> tau') -> term G tau -> term G tau'.

Lemma weakening : forall G D tau, term (G ; D) tau -> 
  forall tau', term (G , tau' ; D) tau.
Proof with simpl in * ; auto ; simpl_depind.
  intros G D tau H.

  dependent induction H generalizing G D.

  destruct D...
    apply weak ; apply ax.
    
    apply ax.
    
  destruct D...
    specialize (IHterm G empty)...
    apply weak...

    apply weak...

  destruct D...
    apply weak ; apply abs ; apply H.

    apply abs...
    specialize (IHterm G0 (D, t, tau))...

  apply app with tau...
Qed.

Lemma exchange : forall G D alpha bet tau, term (G, alpha, bet ; D) tau -> term (G, bet, alpha ; D) tau.
Proof with simpl in * ; simpl_depind ; auto.
  intros until 1.
  dependent induction H generalizing G D alpha bet...

  destruct D...
    apply weak ; apply ax.

    apply ax.

  destruct D...
    pose (weakening (G:=G0) (D:=(empty, alpha)))...

    apply weak...

  apply abs...
  specialize (IHterm G0 (D, tau))...

  eapply app with tau...
Save.
