Require Import Coq.Program.Program Coq.Program.Equality.

Goal forall (H: forall n m : nat, n = m -> n = 0) x, x = tt.
intros.
dependent destruction x.
reflexivity.
Qed.

Variable A : Set.

Inductive vector : nat -> Type := vnil : vector 0 | vcons : A -> forall {n}, vector n -> vector (S n).

Goal forall n, forall v : vector (S n), vector n.
Proof.
  intros n H.
  dependent destruction H.
  assumption.
Qed.

Require Import ProofIrrelevance.

Goal forall n, forall v : vector (S n), exists v' : vector n, exists a : A, v = vcons a v'.
Proof.
  intros n v.
  dependent destruction v.
  exists v ; exists a.
  reflexivity.
Qed.

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

Arguments snoc _%context_scope.

Notation " Γ , τ " := (snoc Γ τ) (at level 25, τ at next level, left associativity) : context_scope.

Fixpoint conc (Δ Γ : ctx) : ctx :=
  match Δ with
    | empty => Γ
    | snoc Δ' x => snoc (conc Δ' Γ) x
  end.

Notation " Γ  ; Δ " := (conc Δ Γ) (at level 25, left associativity) : context_scope.

Reserved Notation " Γ ⊢ τ " (at level 30, no associativity).

Generalizable All Variables.

Inductive term : ctx -> type -> Type :=
| ax : `(Γ, τ ⊢ τ)
| weak : `{Γ ⊢ τ -> Γ, τ' ⊢ τ}
| abs : `{Γ, τ ⊢ τ' -> Γ ⊢ τ --> τ'}
| app : `{Γ ⊢ τ --> τ' -> Γ ⊢ τ -> Γ ⊢ τ'}

where " Γ ⊢ τ " := (term Γ τ) : type_scope.

Hint Constructors term : lambda.

Local Open Scope context_scope.

Ltac eqns := subst ; reverse ; simplify_dep_elim ; simplify_IH_hyps.

Lemma weakening : forall Γ Δ τ, Γ ; Δ ⊢ τ ->
  forall τ', Γ , τ' ; Δ ⊢ τ.
Proof with simpl in * ; eqns ; eauto with lambda.
  intros Γ Δ τ H.

  dependent induction H.

  destruct Δ as [|Δ τ'']...

  destruct Δ as [|Δ τ'']...

  destruct Δ as [|Δ τ'']...
    apply abs.
    specialize (IHterm Γ (Δ, τ'', τ))...

  intro. eapply app...
Defined.

Lemma weakening_ctx : forall Γ Δ τ, Γ ; Δ ⊢ τ ->
  forall Δ', Γ ; Δ' ; Δ ⊢ τ.
Proof with simpl in * ; eqns ; eauto with lambda.
  intros Γ Δ τ H.

  dependent induction H.

  destruct Δ as [|Δ τ'']...
  induction Δ'...

  destruct Δ as [|Δ τ'']...
  induction Δ'...

  destruct Δ as [|Δ τ'']...
    apply abs.
    specialize (IHterm Γ (empty, τ))...

    apply abs.
    specialize (IHterm Γ (Δ, τ'', τ))...

  intro. eapply app...
Defined.

Lemma exchange : forall Γ Δ α β τ, term (Γ, α, β ; Δ) τ -> term (Γ, β, α ; Δ) τ.
Proof with simpl in * ; eqns ; eauto.
  intros until 1.
  dependent induction H.

  destruct Δ ; eqns.
    apply weak ; apply ax.

    apply ax.

  destruct Δ...
    pose (weakening Γ (empty, α))...

    apply weak...

  apply abs...
    specialize (IHterm Γ (Δ, τ))...

  eapply app...
Defined.



(** Example by Andrew Kenedy, uses simplification of the first component of dependent pairs. *)

Set Implicit Arguments.

Inductive Ty :=
 | Nat : Ty
 | Prod : Ty -> Ty -> Ty.

Inductive Exp : Ty -> Type :=
| Const : nat -> Exp Nat
| Pair : forall t1 t2, Exp t1 -> Exp t2 -> Exp (Prod t1 t2)
| Fst : forall t1 t2, Exp (Prod t1 t2) -> Exp t1.

Inductive Ev : forall t, Exp t -> Exp t -> Prop :=
| EvConst   : forall n, Ev (Const n) (Const n)
| EvPair    : forall t1 t2 (e1:Exp t1) (e2:Exp t2) e1' e2',
               Ev e1 e1' -> Ev e2 e2' -> Ev (Pair e1 e2) (Pair e1' e2')
| EvFst     : forall t1 t2 (e:Exp (Prod t1 t2)) e1 e2,
               Ev e (Pair e1 e2) ->
               Ev (Fst e) e1.

Lemma EvFst_inversion : forall t1 t2 (e:Exp (Prod t1 t2)) e1, Ev (Fst e) e1 -> exists e2, Ev e (Pair e1 e2).
intros t1 t2 e e1 ev. dependent destruction ev. exists e2 ; assumption.
Qed.
