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

Notation " Γ , τ " := (snoc Γ τ) (at level 25, t at next level, left associativity).

Fixpoint conc (Γ Δ : ctx) : ctx :=
  match Δ with
    | empty => Γ
    | snoc Δ' x => snoc (conc Γ Δ') x
  end.

Notation " Γ ; Δ " := (conc Γ Δ) (at level 25, left associativity).

Inductive term : ctx -> type -> Type :=
| ax : forall Γ τ, term (Γ, τ) τ
| weak : forall Γ τ, term Γ τ -> forall τ', term (Γ, τ') τ
| abs : forall Γ τ τ', term (Γ , τ) τ' -> term Γ (τ --> τ')
| app : forall Γ τ τ', term Γ (τ --> τ') -> term Γ τ -> term Γ τ'.

Lemma weakening : forall Γ Δ τ, term (Γ ; Δ) τ -> 
  forall τ', term (Γ , τ' ; Δ) τ.
Proof with simpl in * ; auto ; simpl_depind.
  intros Γ Δ τ H.

  dependent induction H generalizing Γ Δ.

  destruct Δ...
    apply weak ; apply ax.
    
    apply ax.
    
  destruct Δ...
    specialize (IHterm Γ empty)...
    apply weak...

    apply weak...

  destruct Δ...
    apply weak ; apply abs ; apply H.

    apply abs...
    specialize (IHterm Γ0 (Δ, t, τ))...

  apply app with τ...
Qed.

Lemma exchange : forall Γ Δ α β τ, term (Γ, α, β ; Δ) τ -> term (Γ, β, α ; Δ) τ.
Proof with simpl in * ; simpl_depind ; auto.
  intros until 1.
  dependent induction H generalizing Γ Δ α β...

  destruct Δ...
    apply weak ; apply ax.

    apply ax.

  destruct Δ...
    pose (weakening (Γ:=Γ0) (Δ:=(empty, α)))...

    apply weak...

  apply abs...
  specialize (IHterm Γ0 (Δ, τ))...

  eapply app with τ...
Save.
