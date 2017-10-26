Require Import Coq.Classes.Equivalence.
Require Import Coq.Program.Program.

Ltac obligations_tactic ::= program_simpl ; simpl_relation.

Lemma bla : forall [ ! Equivalence A (eqA : relation A) ] x y, eqA x y -> eqA y x.
Proof.
  intros.
  rewrite H0.
  reflexivity.
Defined.

Lemma bla' : forall [ ! Equivalence A (eqA : relation A) ] x y, eqA x y -> eqA y x.
Proof.
  intros.
  (* Need delta on [relation] to unify with the right lemmas. *)
  rewrite <- H0.
  reflexivity.
Qed.

Axiom euclid : nat -> { x : nat | x > 0 } -> nat.

Definition eq_proj {A} {s : A -> Prop} : relation (sig s) :=
  fun x y => `x = `y.

Program Instance {A : Type} {s : A -> Prop} => Equivalence (sig s) eq_proj.

  Next Obligation.
  Proof.
    constructor ; red ; intros.
    reflexivity.
  Qed.

  Admit Obligations.

Instance Morphism (eq ==> eq_proj ==> eq) euclid.
Proof.
Admitted.

Goal forall (x : nat) (y : nat | y > 0) (z : nat | z > 0), eq_proj y z -> euclid x y = euclid x z.
Proof.
  intros.
  (* Breaks if too much delta in unification *)
  rewrite H.
  reflexivity.
Qed.
