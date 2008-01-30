Require Import Coq.Program.Program.
Set Implicit Arguments.
Unset Strict Implicit.

Variable A : Set.

Inductive vector : nat -> Type := vnil : vector 0 | vcons : A -> forall n, vector n -> vector (S n).

Goal forall n, forall v : vector (S n), vector n.
Proof.
  intros n H.
  dependent induction H.
  autoinjection.
  assumption.
Save.

Require Import ProofIrrelevance.

Goal forall n, forall v : vector (S n), exists v' : vector n, exists a : A, v = vcons a v'.
Proof.
  intros n H.

  dependent induction H generalizing n.
  inversion H0. subst.
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
| abs : forall G tau tau', term (snoc G tau) tau' -> term G (arrow tau tau')
| app : forall G tau tau', term G (arrow tau tau') -> term G tau -> term G tau'.

Fixpoint conc (G D : ctx) : ctx :=
  match D with
    | empty => G
    | snoc D' x => snoc (conc G D') x
  end.

Hint Unfold conc.

Notation " G ; D " := (conc G D) (at level 20).
Notation " G , D " := (snoc G D) (at level 20,  D at next level).

Lemma weakening : forall G D tau, term (G ; D) tau -> 
  forall tau', term (G , tau' ; D) tau.
Proof with simpl in * ; program_simpl ; simpl_IHs_eqs.
  intros G D tau H.

  dependent induction H generalizing G D...

  destruct D...
    apply weak ; apply ax.
    
    apply ax.

  destruct D...
    do 2 apply weak...

    apply weak...

  destruct D...
    apply weak ; apply abs ; apply H.

    apply abs...
    refine_hyp (IHterm G0 (D, t, tau))...

  apply app with tau...
Qed.

Lemma exchange : forall G D alpha bet tau, term (G, alpha, bet ; D) tau -> term (G, bet, alpha ; D) tau.
Proof with simpl in * ; program_simpl ; simpl_IHs_eqs.
  intros G D alpha bet tau H.
  dependent induction H generalizing G D alpha bet.

  destruct D...
    apply weak ; apply ax.

    apply ax.

  destruct D...
    pose (weakening (G:=G0) (D:=(empty, alpha)))...

    apply weak...

  apply abs.
  refine_hyp (IHterm G0 (D, tau))...

  eapply app with tau...
Qed.