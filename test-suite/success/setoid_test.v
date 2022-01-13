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

Module InType.
Require Import CRelationClasses CMorphisms.

Inductive All {A : Type} (P : A -> Type) : list A -> Type :=
| All_nil : All P nil
| All_cons x (px : P x) xs (pxs : All P xs) : All P (x :: xs).

Lemma All_impl {A} (P Q : A -> Type) l : (forall x, P x -> Q x) -> All P l -> All Q l.
Proof.
  intros HP. induction 1; constructor; eauto.
Qed.

Axiom add_0_r_peq : forall x : nat, eq (x + 0)%nat x.

Instance All_proper {A} :
  CMorphisms.Proper ((pointwise_relation A iffT) ==> eq ==> iffT) All.
Proof.
  intros f g Hfg x y e. destruct e. split; apply All_impl, Hfg.
Qed.

Lemma rewrite_all {l : list nat} (Q : nat -> Type) :
  All (fun x => Q x) l ->
  All (fun x => Q (x + 0)) l.
Proof.
  intros a.
  setoid_rewrite add_0_r_peq.
  exact a.
Qed.

Lemma rewrite_all_in {l : list nat} (Q : nat -> Type) :
  All (fun x => Q (x + 0)) l ->
  All (fun x => Q x) l.
Proof.
  intros a.
  setoid_rewrite add_0_r_peq in a.
  exact a.
Qed.

Lemma rewrite_all_in2 {l : list nat} (Q : nat -> Type) (R : nat -> Type) :
  All (fun x => prod (Q (x + 0)%nat) (R x))%type l ->
  All (fun x => prod (Q x) (R x))%type l.
Proof.
  intros a.
  setoid_rewrite add_0_r_peq in a.
  exact a.
Qed.
End InType.

Module Polymorphism.
Require Import CRelationClasses CMorphisms.

#[universes(polymorphic, cumulative)]
Inductive plist@{i} (A : Type@{i}) : Type@{i} :=
| pnil : plist A
| pcons : A -> plist A -> plist A.
Arguments pnil {A}.
Arguments pcons {A}.
#[universes(polymorphic, cumulative)]
Record pprod@{i j} (A : Type@{i}) (B : Type@{j}) : Type@{max(i, j)} :=
  { pfst : A;
    psnd : B }.
Arguments pfst {A B}.
Arguments psnd {A B}.

Notation "x :: xs" := (pcons x xs).

#[universes(polymorphic)]
Fixpoint All@{i j} {A : Type@{i}} (P : A -> Type@{j}) (l : plist A) : Type@{j} :=
 match l with
 | pnil => unit
 | x :: xs => pprod (P x) (All P xs)
 end.
(*
#[universes(polymorphic, cumulative)]
Inductive All {A : Type} (P : A -> Type) : list A -> Type :=
| All_nil : All P nil
| All_cons x (px : P x) xs (pxs : All P xs) : All P (x :: xs). *)

#[universes(polymorphic)]
Lemma All_impl {A} (P Q : A -> Type) l : (forall x, P x -> Q x) -> All P l -> All Q l.
Proof.
  intros HP.
  induction l; [intros|intros []]; constructor; eauto.
Qed.
Check pointwise_relation.

#[universes(polymorphic)]
Inductive peq@{i} (A : Type@{i}) (a : A) : A -> Type@{i} :=
  peq_refl : peq A a a.

Arguments peq {A}.
Arguments peq_refl {A a}.

#[universes(polymorphic)]
Axiom add_0_r_peq : forall x : nat, peq (x + 0)%nat x.

#[universes(polymorphic)]
Instance peq_left {A : Type} {B : Type} {R : crelation B} (f : A -> B) `{Reflexive B R} : Proper (peq ==> R) f.
Admitted.

Instance reflexive_eq_dom_reflexive@{i j jr mij mijr} {A : Type@{i}} {B : Type@{j}} (R : crelation@{j jr} B) :
  Reflexive@{j jr} R ->
  Reflexive@{mij mijr} (@peq A ==> R)%signature.
Proof.
  intros hr x ? ? e. destruct e. apply hr.
Qed.

#[universes(polymorphic)]
Instance All_proper {A} :
  CMorphisms.Proper ((pointwise_relation A iffT) ==> peq ==> iffT) All.
Proof.
  intros f g Hfg x y e. destruct e. split; apply All_impl, Hfg.
Qed.

#[universes(polymorphic)]
Instance eq_proper_proxy@{i} {A : Type@{i}} (x : A) : ProperProxy@{i i} peq x.
Proof. red. exact peq_refl. Defined.

#[universes(polymorphic)]
Instance peq_equiv {A} : Equivalence (@peq A).
Proof.
  split.
Admitted.

Lemma rewrite_all {l : plist nat} (Q : nat -> Type) :
  All (fun x => Q x) l ->
  All (fun x => Q (x + 0)) l.
Proof.
  intros a.
  setoid_rewrite add_0_r_peq.
  exact a.
Qed.

Lemma rewrite_all_in {l : plist nat} (Q : nat -> Type) :
  All (fun x => Q (x + 0)) l ->
  All (fun x => Q x) l.
Proof.
  intros a.  Show Universes.
  setoid_rewrite add_0_r_peq in a.
  exact a.
Qed.

Lemma rewrite_all_in2 {l : plist nat} (Q : nat -> Type) (R : nat -> Type) :
  All (fun x => pprod (Q (x + 0)%nat) (R x))%type l ->
  All (fun x => pprod (Q x) (R x))%type l.
Proof.
  intros a.
  setoid_rewrite add_0_r_peq in a.
  exact a.
Qed.
End Polymorphism.
