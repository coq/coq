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

unfold same in |- *; split.
red in |- *; auto.

red in |- *.
intros.
elim (H a); auto.

intros.
elim (H a); elim (H0 a).
split; auto.
Qed.

Add Setoid set same setoid_set as setsetoid.

Add Morphism In : In_ext.
unfold same in |- *; intros a s t H; elim (H a); auto.
Qed.

Lemma add_aux :
 forall s t : set,
 same s t -> forall a b : A, In a (Add b s) -> In a (Add b t).
unfold same in |- *; simple induction 2; intros.
rewrite H1.
simpl in |- *; left; reflexivity.

elim (H a).
intros.
simpl in |- *; right.
apply (H2 H1).
Qed.

Add Morphism Add : Add_ext.
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

unfold same in |- *.
split.
simpl in |- *.
case (eq_dec a a).
intros e ff; elim ff.

intros; absurd (a = a); trivial.

simpl in |- *.
intro H; elim H.
Qed.

Parameter P : set -> Prop.
Parameter P_ext : forall s t : set, same s t -> P s -> P t.

Add Morphism P : P_extt.
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

Instance DefaultRelation (id A) (rel A).

Add Morphism (@f A) : f_morph.
Proof.
unfold rel, f. trivial.
Qed.
