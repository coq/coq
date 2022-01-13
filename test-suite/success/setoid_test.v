Require Import TestSuite.admit.
Require Import Setoid.

Parameter A : Set.

Axiom eq_dec : forall a b : A, {a = b} + {a <> b}.

Inductive set : Set :=
  | Empty : set
  | Add : A -> set -> set.

Fixpoint In (a : A) (s : set) {struct s} : Prop :=
  match s with
  | Empty => False
  | Add b s' => a = b \/ In a s'
  end.

Definition same (s t : set) : Prop := forall a : A, In a s <-> In a t.

Lemma setoid_set : Setoid_Theory set same.

unfold same; split ; red.
red; auto.

red.
intros.
elim (H a); auto.

intros.
elim (H a); elim (H0 a).
split; auto.
Qed.

Add Setoid set same setoid_set as setsetoid.

Add Morphism In with signature (eq ==> same ==> iff) as In_ext.
Proof.
unfold same; intros a s t H; elim (H a); auto.
Qed.

Lemma add_aux :
 forall s t : set,
 same s t -> forall a b : A, In a (Add b s) -> In a (Add b t).
unfold same; simple induction 2; intros.
rewrite H1.
simpl; left; reflexivity.

elim (H a).
intros.
simpl; right.
apply (H2 H1).
Qed.

Add Morphism Add with signature (eq ==> same ==> same) as Add_ext.
split; apply add_aux.
assumption.
rewrite H.
reflexivity.
Qed.

Fixpoint remove (a : A) (s : set) {struct s} : set :=
  match s with
  | Empty => Empty
  | Add b t =>
      match eq_dec a b with
      | left _ => remove a t
      | right _ => Add b (remove a t)
      end
  end.

Lemma in_rem_not : forall (a : A) (s : set), ~ In a (remove a (Add a Empty)).

intros.
setoid_replace (remove a (Add a Empty)) with Empty.

auto.

unfold same.
split.
simpl.
case (eq_dec a a).
intros e ff; elim ff.

intros; absurd (a = a); trivial.

simpl.
intro H; elim H.
Qed.

Parameter P : set -> Prop.
Parameter P_ext : forall s t : set, same s t -> P s -> P t.

Add Morphism P with signature (same ==> iff) as P_extt.
intros; split; apply P_ext; (assumption || apply (Seq_sym _ _ setoid_set); assumption).
Qed.

Lemma test_rewrite :
 forall (a : A) (s t : set), same s t -> P (Add a s) -> P (Add a t).
intros.
rewrite <- H.
rewrite H.
setoid_rewrite <- H.
setoid_rewrite H.
setoid_rewrite <- H.
trivial.
Qed.

(* Unifying the domain up to delta-conversion (example from emakarov) *)

Definition id: Set -> Set := fun A => A.
Definition rel : forall A : Set, relation (id A) := @eq.
Definition f: forall A : Set, A -> A := fun A x => x.

Add Relation (id A) (rel A) as eq_rel.

Add Morphism (@f A) with signature (eq ==> eq) as f_morph.
Proof.
unfold rel, f. trivial.
Qed.

(* Submitted by Nicolas Tabareau *)
(* Needs unification.ml to support environments with de Bruijn *)

Goal forall
  (f : Prop -> Prop)
  (Q : (nat -> Prop) -> Prop)
  (H : forall (h : nat -> Prop), Q (fun x : nat => f (h x)) <-> True)
  (h:nat -> Prop),
  Q (fun x : nat => f (Q (fun b : nat => f (h x)))) <-> True.
intros f0 Q H.
setoid_rewrite H.
tauto.
Qed.

(** Check proper refreshing of the lemma application for multiple 
   different instances in a single setoid rewrite. *)

Section mult.
  Context (fold : forall {A} {B}, (A -> B) -> A -> B).
  Context (add : forall A, A -> A).
  Context (fold_lemma : forall {A B f} {eqA : relation B} x, eqA (fold A B f (add A x)) (fold _ _ f x)).
  Context (ab : forall B, A -> B).
  Context (anat : forall A, nat -> A).

Goal forall x, (fold _ _ (fun x => ab A x) (add A x) = anat _ (fold _ _ (ab nat) (add _ x))). 
Proof. intros.
  setoid_rewrite fold_lemma. 
  change (fold A A (fun x0 : A => ab A x0) x = anat A (fold A nat (ab nat) x)).
Abort.

End mult.

(** Current semantics for rewriting with typeclass constraints in the lemma 
   does not fix the instance at the first unification, use [at], or simply rewrite for 
   this semantics. *)

Parameter beq_nat : forall x y : nat, bool.

Class Foo (A : Type) := {foo_neg : A -> A ; foo_prf : forall x : A, x = foo_neg x}.
Instance: Foo nat. admit. Defined.
Instance: Foo bool. admit. Defined.

Goal forall (x : nat) (y : bool), beq_nat (foo_neg x) 0 = foo_neg y.
Proof. intros. setoid_rewrite <- foo_prf. change (beq_nat x 0 = y). Abort.

Goal forall (x : nat) (y : bool), beq_nat (foo_neg x) 0 = foo_neg y.
Proof. intros. setoid_rewrite <- @foo_prf at 1. change (beq_nat x 0 = foo_neg y). Abort.

(* This should not raise an anomaly as it did for some time in early 2016 *)

Definition t := nat -> bool.
Definition h (a b : t) := forall n, a n = b n.

Instance subrelh : subrelation h (Morphisms.pointwise_relation nat eq).
Proof. intros x y H; assumption. Qed.

Goal forall a b, h a b -> a 0 = b 0.
intros.
setoid_rewrite H. (* Fallback on ordinary rewrite without anomaly *)
reflexivity.
Qed.
