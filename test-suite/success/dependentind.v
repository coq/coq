Require Import Coq.Program.Program.
Set Manual Implicit Arguments.


Variable A : Set.

Inductive vector : nat -> Type := vnil : vector 0 | vcons : A -> forall {n}, vector n -> vector (S n).

Goal forall n, forall v : vector (S n), vector n.
Proof.
  intros n H.
  dependent destruction H.
  assumption.
Save.

Require Import ProofIrrelevance.

Goal forall n, forall v : vector (S n), exists v' : vector n, exists a : A, v = vcons a v'.
Proof.
  intros n v.
  dependent destruction v.
  exists v ; exists a.
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

Bind Scope context_scope with ctx.
Delimit Scope context_scope with ctx.

Arguments Scope snoc [context_scope].

Notation " Γ ,, τ " := (snoc Γ τ) (at level 25, t at next level, left associativity).

Fixpoint conc (Δ Γ : ctx) : ctx :=
  match Δ with
    | empty => Γ
    | snoc Δ' x => snoc (conc Δ' Γ) x
  end.

Notation " Γ ;; Δ " := (conc Δ Γ) (at level 25, left associativity) : context_scope.

Inductive term : ctx -> type -> Type :=
| ax : forall Γ τ, term (snoc Γ τ) τ
| weak : forall Γ τ, term Γ τ -> forall τ', term (Γ ,, τ') τ
| abs : forall Γ τ τ', term (snoc Γ τ) τ' -> term Γ (τ --> τ')
| app : forall Γ τ τ', term Γ (τ --> τ') -> term Γ τ -> term Γ τ'.

Hint Constructors term : lambda.

Notation " Γ |-- τ " := (term Γ τ) (at level 0) : type_scope.

Lemma weakening : forall Γ Δ τ, term (Γ ;; Δ) τ -> 
  forall τ', term (Γ ,, τ' ;; Δ) τ.
Proof with simpl in * ; simplify_dep_elim ; simplify_IH_hyps ; eauto with lambda.
  intros Γ Δ τ H.

  dependent induction H.

  destruct Δ...

  destruct Δ...

  destruct Δ...
    apply abs...
    
    specialize (IHterm (Δ,, t,, τ)%ctx Γ0)...

  intro.
  apply app with τ...
Qed.

Lemma exchange : forall Γ Δ α β τ, term (Γ,, α,, β ;; Δ) τ -> term (Γ,, β,, α ;; Δ) τ.
Proof with simpl in * ; simplify_dep_elim ; simplify_IH_hyps ; auto.
  intros until 1.
  dependent induction H.

  destruct Δ...
    apply weak ; apply ax.

    apply ax.

  destruct Δ...
    pose (weakening Γ0 (empty,, α))...

    apply weak...

  apply abs... 
  specialize (IHterm (Δ ,, τ))...

  eapply app with τ...
Save.
