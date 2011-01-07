(* A bit complex but realistic example whose last fixpoint definition
   used to fail in 8.1 because of wrong environment in conversion
   problems (see revision 9664) *)

Require Import List.
Require Import Arith.

Parameter predicate : Set.
Parameter function : Set.
Definition variable := nat.
Definition x0 := 0.
Definition var_eq_dec := eq_nat_dec.

Inductive term : Set :=
  | App : function -> term -> term
  | Var : variable -> term.

Definition atom := (predicate * term)%type.

Inductive formula : Set :=
  | Atom : atom -> formula
  | Imply : formula -> formula -> formula
  | Forall : variable -> formula -> formula.

Notation "A --> B" := (Imply A B) (at level 40).

Definition substitution range := list (variable * range).

Fixpoint remove_assoc (A:Set)(x:variable)(rho: substitution A){struct rho}
                      : substitution A :=
  match rho with
    | nil => rho
    | (y,t) :: rho => if var_eq_dec x y then remove_assoc A x rho
                      else (y,t) :: remove_assoc A x rho
  end.

Fixpoint assoc (A:Set)(x:variable)(rho:substitution A){struct rho}
               : option A :=
  match rho with
    | nil => None
    | (y,t) :: rho => if var_eq_dec x y then Some t
                      else assoc A x rho
  end.

Fixpoint subst_term (rho:substitution term)(t:term){struct t} : term :=
  match t with
  | Var x => match assoc _ x rho with
             | Some a => a
             | None => Var x
             end
  | App f t' => App f (subst_term rho t')
  end.

Fixpoint subst_formula (rho:substitution term)(A:formula){struct A}:formula :=
  match A with
  | Atom (p,t) => Atom (p, subst_term rho t)
  | A --> B => subst_formula rho A --> subst_formula rho B
  | Forall y A => Forall y (subst_formula (remove_assoc _ y rho) A)
  (* assume t closed *)
  end.

Definition subst A x t := subst_formula ((x,t):: nil) A.

Record Kripke : Type := {
  worlds: Set;
  wle : worlds -> worlds -> Type;
  wle_refl : forall w, wle w w ;
  wle_trans : forall w w' w'', wle w w' -> wle w' w'' -> wle w w'';
  domain : Set;
  vars : variable -> domain;
  funs : function -> domain -> domain;
  atoms : worlds -> predicate * domain -> Type;
  atoms_mon : forall w w', wle w w' -> forall P, atoms w P -> atoms w' P
}.

Section Sem.

Variable K : Kripke.

Fixpoint sem (rho: substitution (domain K))(t:term){struct t} : domain K :=
  match t with
  | Var x => match assoc _ x rho with
             | Some a => a
             | None => vars K x
             end
  | App f t' => funs K f (sem rho t')
  end.

End Sem.

Notation "w <= w'" := (wle _ w w').

Set Implicit Arguments.

Reserved Notation "w ||- A" (at level 70).

Definition context := list formula.

Variable fresh : variable -> context -> Prop.

Variable fresh_out : context -> variable.

Axiom fresh_out_spec : forall Gamma, fresh (fresh_out Gamma) Gamma.

Axiom fresh_peel : forall x A Gamma, fresh x (A::Gamma) -> fresh x Gamma.

Fixpoint force (K:Kripke)(rho: substitution (domain K))(w:worlds K)(A:formula)
               {struct A} : Type :=
  match A with
  | Atom (p,t) => atoms K w (p, sem K rho t)
  | A --> B => forall w', w <= w' -> force K rho w' A -> force K rho w' B
  | Forall x A => forall w', w <= w' -> forall t, force K ((x,t)::remove_assoc _ x rho) w' A
  end.

Notation "w ||- A" := (force _ nil w A).

Reserved Notation "Gamma |- A" (at level 70).
Reserved Notation "Gamma ; A |- C" (at level 70, A at next level).

Inductive context_prefix (Gamma:context) : context -> Type :=
  | CtxPrefixRefl : context_prefix Gamma Gamma
  | CtxPrefixTrans : forall A Gamma', context_prefix Gamma Gamma' -> context_prefix Gamma (cons A Gamma').

Inductive in_context (A:formula) : list formula -> Prop :=
  | InAxiom : forall Gamma, in_context A (cons A Gamma)
  | OmWeak : forall Gamma B, in_context A Gamma -> in_context A (cons B Gamma).

Inductive prove : list formula -> formula -> Type :=
  | ProofImplyR : forall A B Gamma, prove (cons A Gamma) B
    -> prove Gamma (A --> B)
  | ProofForallR : forall x A Gamma, (forall y, fresh y (A::Gamma)
    -> prove Gamma (subst A x (Var y))) -> prove Gamma (Forall x A)
  | ProofCont : forall A Gamma Gamma' C, context_prefix (A::Gamma) Gamma'
    -> (prove_stoup Gamma' A C) -> (Gamma' |- C)

where "Gamma |- A" := (prove Gamma A)

  with prove_stoup : list formula -> formula -> formula -> Type :=
  | ProofAxiom Gamma C: Gamma ; C |- C
  | ProofImplyL Gamma C : forall A B, (Gamma |- A)
    -> (prove_stoup Gamma B C) -> (prove_stoup Gamma (A --> B) C)
  | ProofForallL Gamma C : forall x t A, (prove_stoup Gamma (subst A x t) C)
    -> (prove_stoup Gamma (Forall x A) C)

where " Gamma ; B |- A " := (prove_stoup Gamma B A).

Axiom context_prefix_trans :
  forall Gamma Gamma' Gamma'',
    context_prefix Gamma Gamma'
      -> context_prefix Gamma' Gamma''
        -> context_prefix Gamma Gamma''.

Axiom Weakening :
  forall Gamma Gamma' A,
    context_prefix Gamma Gamma' -> Gamma |- A -> Gamma' |- A.

Axiom universal_weakening :
  forall Gamma Gamma', context_prefix Gamma Gamma'
    -> forall P, Gamma |- Atom P -> Gamma' |- Atom P.

Canonical Structure Universal := Build_Kripke
  context
  context_prefix
  CtxPrefixRefl
  context_prefix_trans
  term
  Var
  App
  (fun Gamma P => Gamma |- Atom P)
  universal_weakening.

Axiom subst_commute :
  forall A rho x t,
    subst_formula ((x,t)::rho) A = subst (subst_formula rho A) x t.

Axiom subst_formula_atom :
  forall rho p t,
    Atom (p, sem _ rho t) = subst_formula rho (Atom (p,t)).

Fixpoint universal_completeness (Gamma:context)(A:formula){struct A}
  : forall rho:substitution term,
      force _ rho Gamma A -> Gamma |- subst_formula rho A
  :=
  match A
    return forall rho, force _ rho Gamma A
      -> Gamma |- subst_formula rho A
  with
  | Atom (p,t) => fun rho H => eq_rect _ (fun A => Gamma |- A) H _ (subst_formula_atom rho p t)
  | A --> B => fun rho HImplyAB =>
    let A' := subst_formula rho A in
    ProofImplyR (universal_completeness (A'::Gamma) B rho
     (HImplyAB (A'::Gamma)(CtxPrefixTrans A' (CtxPrefixRefl Gamma))
       (universal_completeness_stoup A rho (fun C Gamma' Hle p
         => ProofCont Hle p))))
  | Forall x A => fun rho HForallA
    => ProofForallR x (fun y Hfresh
      => eq_rect _ _ (universal_completeness Gamma A _
        (HForallA Gamma (CtxPrefixRefl Gamma)(Var y))) _ (subst_commute _ _ _ _ ))
  end
with universal_completeness_stoup (Gamma:context)(A:formula){struct A}
  : forall rho, (forall C Gamma', context_prefix Gamma Gamma'
    -> Gamma' ; subst_formula rho A |- C -> Gamma' |- C)
      -> force _ rho Gamma A
  :=
  match A return forall rho,
    (forall C Gamma', context_prefix Gamma Gamma'
     -> Gamma' ; subst_formula rho A |- C
     -> Gamma' |- C)
       -> force _ rho Gamma A
  with
  | Atom (p,t) as C => fun rho H
    => H _ Gamma (CtxPrefixRefl Gamma)(ProofAxiom _ _)
  | A --> B => fun rho H => fun Gamma' Hle HA
    => universal_completeness_stoup B rho (fun C Gamma'' Hle' p
      => H C Gamma'' (context_prefix_trans Hle Hle')
         (ProofImplyL (Weakening Hle' (universal_completeness Gamma' A rho HA)) p))
  | Forall x A => fun rho H => fun Gamma' Hle t
    => (universal_completeness_stoup A ((x,t)::remove_assoc _ x rho)
        (fun C Gamma'' Hle' p =>
          H C Gamma'' (context_prefix_trans Hle Hle')
          (ProofForallL x t (subst_formula (remove_assoc _ x rho) A)
          (eq_rect _ (fun D => Gamma'' ; D |- C) p _ (subst_commute _ _ _ _)))))
  end.


(* A simple example that raised an uncaught exception at some point *)

Fail Check fun x => @eq_refl x <: true = true.
