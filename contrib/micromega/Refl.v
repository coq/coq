(********************************************************************)
(*                                                                  *)
(* Micromega: A reflexive tactics using the Positivstellensatz *)
(*                                                                  *)
(*  Frédéric Besson (Irisa/Inria) 2006				    *)
(*                                                                  *)
(********************************************************************)
Require Import List.

Set Implicit Arguments.

(* Refl of '->' '/\': basic properties *)

Fixpoint make_impl (A : Type) (eval : A -> Prop) (l : list A) (goal : Prop) {struct l} : Prop :=
  match l with
    | nil => goal
    | cons e l => (eval e) -> (make_impl eval l goal)
  end.

Theorem make_impl_true :
  forall (A : Type) (eval : A -> Prop) (l : list A), make_impl eval l True.
Proof.
induction l as [| a l IH]; simpl.
trivial.
intro; apply IH.
Qed.

Fixpoint make_conj (A : Type) (eval : A -> Prop) (l : list A) {struct l} : Prop :=
  match l with
    | nil => True
    | cons e nil => (eval e)
    | cons e l2 => ((eval e) /\ (make_conj eval l2))
  end.

Theorem make_conj_cons : forall (A : Type) (eval : A -> Prop) (a : A) (l : list A),
  make_conj eval (a :: l) <-> eval a /\ make_conj eval l.
Proof.
intros; destruct l; simpl; tauto.
Qed.

Lemma make_conj_impl : forall (A : Type) (eval : A -> Prop) (l : list A) (g : Prop),
  (make_conj eval l -> g) <-> make_impl eval l g.
Proof.
  induction l.
  simpl.
  tauto.
  simpl.
  intros.
  destruct l.
  simpl.
  tauto.
  generalize (IHl g).
  tauto.
Qed.

Lemma make_conj_in : forall (A : Type) (eval : A -> Prop) (l : list A),
  make_conj eval l -> (forall p, In p l -> eval p).
Proof.
  induction l.
  simpl.
  tauto.
  simpl.
  intros.
  destruct l.
  simpl in H0.
  destruct H0.
  subst; auto.
  tauto.
  destruct H.
  destruct H0.
  subst;auto.
  apply IHl; auto.
Qed.

