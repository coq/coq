(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Typeclass-based morphism definition and standard, minimal instances

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.

Generalizable All Variables.
Local Obligation Tactic := simpl_relation.

(** * Morphisms.

   We now turn to the definition of [Proper] and declare standard instances.
   These will be used by the [setoid_rewrite] tactic later. *)

(** A morphism for a relation [R] is a proper element of the relation.
   The relation [R] will be instantiated by [respectful] and [A] by an arrow
   type for usual morphisms. *)

Class Proper {A} (R : relation A) (m : A) : Prop :=
  proper_prf : R m m.

(** Respectful morphisms. *)

(** The fully dependent version, not used yet. *)

Definition respectful_hetero
  (A B : Type)
  (C : A -> Type) (D : B -> Type)
  (R : A -> B -> Prop)
  (R' : forall (x : A) (y : B), C x -> D y -> Prop) :
    (forall x : A, C x) -> (forall x : B, D x) -> Prop :=
    fun f g => forall x y, R x y -> R' x y (f x) (g y).

(** The non-dependent version is an instance where we forget dependencies. *)

Definition respectful {A B : Type}
  (R : relation A) (R' : relation B) : relation (A -> B) :=
  Eval compute in @respectful_hetero A A (fun _ => B) (fun _ => B) R (fun _ _ => R').

(** Notations reminiscent of the old syntax for declaring morphisms. *)

Delimit Scope signature_scope with signature.

Arguments Scope Proper [type_scope signature_scope].
Arguments Scope respectful [type_scope type_scope signature_scope signature_scope].

Module ProperNotations.

  Notation " R ++> R' " := (@respectful _ _ (R%signature) (R'%signature))
    (right associativity, at level 55) : signature_scope.

  Notation " R ==> R' " := (@respectful _ _ (R%signature) (R'%signature))
    (right associativity, at level 55) : signature_scope.

  Notation " R --> R' " := (@respectful _ _ (inverse (R%signature)) (R'%signature))
    (right associativity, at level 55) : signature_scope.

End ProperNotations.

Export ProperNotations.

Open Local Scope signature_scope.

(** Dependent pointwise lifting of a relation on the range. *)

Definition forall_relation {A : Type} {B : A -> Type} (sig : Π a : A, relation (B a)) : relation (Π x : A, B x) :=
  λ f g, Π a : A, sig a (f a) (g a).

Arguments Scope forall_relation [type_scope type_scope signature_scope].

(** Non-dependent pointwise lifting *)

Definition pointwise_relation (A : Type) {B : Type} (R : relation B) : relation (A -> B) :=
  Eval compute in forall_relation (B:=λ _, B) (λ _, R).

Lemma pointwise_pointwise A B (R : relation B) :
  relation_equivalence (pointwise_relation A R) (@eq A ==> R).
Proof. intros. split. simpl_relation. firstorder. Qed.

(** We can build a PER on the Coq function space if we have PERs on the domain and
   codomain. *)

Hint Unfold Reflexive : core.
Hint Unfold Symmetric : core.
Hint Unfold Transitive : core.

Typeclasses Opaque respectful pointwise_relation forall_relation.

Program Instance respectful_per `(PER A R, PER B R') : PER (R ==> R').

  Next Obligation.
  Proof with auto.
    assert(R x0 x0).
    transitivity y0... symmetry...
    transitivity (y x0)...
  Qed.

(** Subrelations induce a morphism on the identity. *)

Instance subrelation_id_proper `(subrelation A R₁ R₂) : Proper (R₁ ==> R₂) id.
Proof. firstorder. Qed.

(** The subrelation property goes through products as usual. *)

Lemma subrelation_respectful `(subl : subrelation A R₂ R₁, subr : subrelation B S₁ S₂) :
  subrelation (R₁ ==> S₁) (R₂ ==> S₂).
Proof. simpl_relation. apply subr. apply H. apply subl. apply H0. Qed.

(** And of course it is reflexive. *)

Lemma subrelation_refl A R : @subrelation A R R.
Proof. simpl_relation. Qed.

Ltac subrelation_tac T U :=
  (is_ground T ; is_ground U ; class_apply @subrelation_refl) ||
    class_apply @subrelation_respectful || class_apply @subrelation_refl.

Hint Extern 3 (@subrelation _ ?T ?U) => subrelation_tac T U : typeclass_instances.

(** [Proper] is itself a covariant morphism for [subrelation]. *)

Lemma subrelation_proper `(mor : Proper A R₁ m, unc : Unconvertible (relation A) R₁ R₂,
  sub : subrelation A R₁ R₂) : Proper R₂ m.
Proof.
  intros. apply sub. apply mor.
Qed.

CoInductive apply_subrelation : Prop := do_subrelation.

Ltac proper_subrelation :=
  match goal with
    [ H : apply_subrelation |- _ ] => clear H ; class_apply @subrelation_proper
  end.

Hint Extern 5 (@Proper _ ?H _) => proper_subrelation : typeclass_instances.

Instance proper_subrelation_proper :
  Proper (subrelation ++> eq ==> impl) (@Proper A).
Proof. reduce. subst. firstorder. Qed.

(** Essential subrelation instances for [iff], [impl] and [pointwise_relation]. *)

Instance iff_impl_subrelation : subrelation iff impl | 2.
Proof. firstorder. Qed.

Instance iff_inverse_impl_subrelation : subrelation iff (inverse impl) | 2.
Proof. firstorder. Qed.

Instance pointwise_subrelation {A} `(sub : subrelation B R R') :
  subrelation (pointwise_relation A R) (pointwise_relation A R') | 4.
Proof. reduce. unfold pointwise_relation in *. apply sub. apply H. Qed.

(** For dependent function types. *)
Lemma forall_subrelation A (B : A -> Type) (R S : forall x : A, relation (B x)) :
  (forall a, subrelation (R a) (S a)) -> subrelation (forall_relation R) (forall_relation S).
Proof. reduce. apply H. apply H0. Qed.

(** We use an extern hint to help unification. *)

Hint Extern 4 (subrelation (@forall_relation ?A ?B ?R) (@forall_relation _ _ ?S)) =>
  apply (@forall_subrelation A B R S) ; intro : typeclass_instances.

(** Any symmetric relation is equal to its inverse. *)

Lemma subrelation_symmetric A R `(Symmetric A R) : subrelation (inverse R) R.
Proof. reduce. red in H0. symmetry. assumption. Qed.

Hint Extern 4 (subrelation (inverse _) _) => 
  class_apply @subrelation_symmetric : typeclass_instances.

(** The complement of a relation conserves its proper elements. *)

Program Instance complement_proper
  `(mR : Proper (A -> A -> Prop) (RA ==> RA ==> iff) R) :
  Proper (RA ==> RA ==> iff) (complement R).

  Next Obligation.
  Proof.
    unfold complement.
    pose (mR x y H x0 y0 H0).
    intuition.
  Qed.

(** The [inverse] too, actually the [flip] instance is a bit more general. *)

Program Instance flip_proper
  `(mor : Proper (A -> B -> C) (RA ==> RB ==> RC) f) :
  Proper (RB ==> RA ==> RC) (flip f).

  Next Obligation.
  Proof.
    apply mor ; auto.
  Qed.

(** Every Transitive relation gives rise to a binary morphism on [impl],
   contravariant in the first argument, covariant in the second. *)

Program Instance trans_contra_co_morphism
  `(Transitive A R) : Proper (R --> R ++> impl) R.

  Next Obligation.
  Proof with auto.
    transitivity x...
    transitivity x0...
  Qed.

(** Proper declarations for partial applications. *)

Program Instance trans_contra_inv_impl_morphism
  `(Transitive A R) : Proper (R --> inverse impl) (R x) | 3.

  Next Obligation.
  Proof with auto.
    transitivity y...
  Qed.

Program Instance trans_co_impl_morphism
  `(Transitive A R) : Proper (R ++> impl) (R x) | 3.

  Next Obligation.
  Proof with auto.
    transitivity x0...
  Qed.

Program Instance trans_sym_co_inv_impl_morphism
  `(PER A R) : Proper (R ++> inverse impl) (R x) | 3.

  Next Obligation.
  Proof with auto.
    transitivity y... symmetry...
  Qed.

Program Instance trans_sym_contra_impl_morphism
  `(PER A R) : Proper (R --> impl) (R x) | 3.

  Next Obligation.
  Proof with auto.
    transitivity x0... symmetry...
  Qed.

Program Instance per_partial_app_morphism
  `(PER A R) : Proper (R ==> iff) (R x) | 2.

  Next Obligation.
  Proof with auto.
    split. intros ; transitivity x0...
    intros.
    transitivity y...
    symmetry...
  Qed.

(** Every Transitive relation induces a morphism by "pushing" an [R x y] on the left of an [R x z] proof
   to get an [R y z] goal. *)

Program Instance trans_co_eq_inv_impl_morphism
  `(Transitive A R) : Proper (R ==> (@eq A) ==> inverse impl) R | 2.

  Next Obligation.
  Proof with auto.
    transitivity y...
  Qed.

(** Every Symmetric and Transitive relation gives rise to an equivariant morphism. *)

Program Instance PER_morphism `(PER A R) : Proper (R ==> R ==> iff) R | 1.

  Next Obligation.
  Proof with auto.
    split ; intros.
    transitivity x0... transitivity x... symmetry...

    transitivity y... transitivity y0... symmetry...
  Qed.

Lemma symmetric_equiv_inverse `(Symmetric A R) : relation_equivalence R (flip R).
Proof. firstorder. Qed.

Program Instance compose_proper A B C R₀ R₁ R₂ :
  Proper ((R₁ ==> R₂) ==> (R₀ ==> R₁) ==> (R₀ ==> R₂)) (@compose A B C).

  Next Obligation.
  Proof.
    simpl_relation.
    unfold compose. apply H. apply H0. apply H1.
  Qed.

(** Coq functions are morphisms for Leibniz equality,
   applied only if really needed. *)

Instance reflexive_eq_dom_reflexive (A : Type) `(Reflexive B R') :
  Reflexive (@Logic.eq A ==> R').
Proof. simpl_relation. Qed.

(** [respectful] is a morphism for relation equivalence. *)

Instance respectful_morphism :
  Proper (relation_equivalence ++> relation_equivalence ++> relation_equivalence) (@respectful A B).
Proof.
  reduce.
  unfold respectful, relation_equivalence, predicate_equivalence in * ; simpl in *.
  split ; intros.

    rewrite <- H0.
    apply H1.
    rewrite H.
    assumption.

    rewrite H0.
    apply H1.
    rewrite <- H.
    assumption.
Qed.

(** Every element in the carrier of a reflexive relation is a morphism for this relation.
   We use a proxy class for this case which is used internally to discharge reflexivity constraints.
   The [Reflexive] instance will almost always be used, but it won't apply in general to any kind of
   [Proper (A -> B) _ _] goal, making proof-search much slower. A cleaner solution would be to be able
   to set different priorities in different hint bases and select a particular hint database for
   resolution of a type class constraint.*)

Class ProperProxy {A} (R : relation A) (m : A) : Prop :=
  proper_proxy : R m m.

Lemma eq_proper_proxy A (x : A) : ProperProxy (@eq A) x.
Proof. firstorder. Qed.

Lemma reflexive_proper_proxy `(Reflexive A R) (x : A) : ProperProxy R x.
Proof. firstorder. Qed.

Lemma proper_proper_proxy `(Proper A R x) : ProperProxy R x.
Proof. firstorder. Qed.

Hint Extern 1 (ProperProxy _ _) => 
  class_apply @eq_proper_proxy || class_apply @reflexive_proper_proxy : typeclass_instances.
Hint Extern 2 (ProperProxy ?R _) => not_evar R; class_apply @proper_proper_proxy : typeclass_instances.

(** [R] is Reflexive, hence we can build the needed proof. *)

Lemma Reflexive_partial_app_morphism `(Proper (A -> B) (R ==> R') m, ProperProxy A R x) :
   Proper R' (m x).
Proof. simpl_relation. Qed.

Class Params {A : Type} (of : A) (arity : nat).

Class PartialApplication.

CoInductive normalization_done : Prop := did_normalization.

Ltac partial_application_tactic :=
  let rec do_partial_apps H m :=
    match m with
      | ?m' ?x => class_apply @Reflexive_partial_app_morphism ; [do_partial_apps H m'|clear H]
      | _ => idtac
    end
  in
  let rec do_partial H ar m :=
    match ar with
      | 0 => do_partial_apps H m
      | S ?n' =>
        match m with
          ?m' ?x => do_partial H n' m'
        end
    end
  in
  let on_morphism m :=
    let m' := fresh in head_of_constr m' m ;
    let n := fresh in evar (n:nat) ;
    let v := eval compute in n in clear n ;
    let H := fresh in
      assert(H:Params m' v) by typeclasses eauto ;
      let v' := eval compute in v in subst m';
      do_partial H v' m
 in
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | [ _ : @Params _ _ _ |- _ ] => fail 1
    | [ |- @Proper ?T _ (?m ?x) ] =>
      match goal with
        | [ _ : PartialApplication |- _ ] =>
          class_apply @Reflexive_partial_app_morphism
        | _ =>
          on_morphism (m x) ||
            (class_apply @Reflexive_partial_app_morphism ;
              [ pose Build_PartialApplication | idtac ])
      end
  end.

Hint Extern 4 (@Proper _ _ _) => partial_application_tactic : typeclass_instances.

Lemma inverse_respectful : forall (A : Type) (R : relation A) (B : Type) (R' : relation B),
  relation_equivalence (inverse (R ==> R')) (inverse R ==> inverse R').
Proof.
  intros.
  unfold flip, respectful.
  split ; intros ; intuition.
Qed.

(** Special-purpose class to do normalization of signatures w.r.t. inverse. *)

Class Normalizes (A : Type) (m : relation A) (m' : relation A) : Prop :=
  normalizes : relation_equivalence m m'.

(** Current strategy: add [inverse] everywhere and reduce using [subrelation]
   afterwards. *)

Lemma inverse_atom A R : Normalizes A R (inverse (inverse R)).
Proof.
  firstorder.
Qed.

Lemma inverse_arrow `(NA : Normalizes A R (inverse R'''), NB : Normalizes B R' (inverse R'')) :
  Normalizes (A -> B) (R ==> R') (inverse (R''' ==> R'')%signature).
Proof. unfold Normalizes in *. intros.
  rewrite NA, NB. firstorder.
Qed.

Ltac inverse :=
  match goal with
    | [ |- Normalizes _ (respectful _ _) _ ] => class_apply @inverse_arrow
    | _ => class_apply @inverse_atom
  end.

Hint Extern 1 (Normalizes _ _ _) => inverse : typeclass_instances.

(** Treating inverse: can't make them direct instances as we
   need at least a [flip] present in the goal. *)

Lemma inverse1 `(subrelation A R' R) : subrelation (inverse (inverse R')) R.
Proof. firstorder. Qed.

Lemma inverse2 `(subrelation A R R') : subrelation R (inverse (inverse R')).
Proof. firstorder. Qed.

Hint Extern 1 (subrelation (flip _) _) => class_apply @inverse1 : typeclass_instances.
Hint Extern 1 (subrelation _ (flip _)) => class_apply @inverse2 : typeclass_instances.

(** That's if and only if *)

Lemma eq_subrelation `(Reflexive A R) : subrelation (@eq A) R.
Proof. simpl_relation. Qed.

(* Hint Extern 3 (subrelation eq ?R) => not_evar R ; class_apply eq_subrelation : typeclass_instances. *)

(** Once we have normalized, we will apply this instance to simplify the problem. *)

Definition proper_inverse_proper `(mor : Proper A R m) : Proper (inverse R) m := mor.

Hint Extern 2 (@Proper _ (flip _) _) => class_apply @proper_inverse_proper : typeclass_instances.

(** Bootstrap !!! *)

Instance proper_proper : Proper (relation_equivalence ==> eq ==> iff) (@Proper A).
Proof.
  simpl_relation.
  reduce in H.
  split ; red ; intros.
  setoid_rewrite <- H.
  apply H0.
  setoid_rewrite H.
  apply H0.
Qed.

Lemma proper_normalizes_proper `(Normalizes A R0 R1, Proper A R1 m) : Proper R0 m.
Proof.
  intros A R0 R1 H m H'.
  red in H, H'.
  setoid_rewrite H.
  assumption.
Qed.

Ltac proper_normalization :=
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | [ _ : apply_subrelation |- @Proper _ ?R _ ] => let H := fresh "H" in
      set(H:=did_normalization) ; class_apply @proper_normalizes_proper
  end.

Hint Extern 6 (@Proper _ _ _) => proper_normalization : typeclass_instances.

(** Every reflexive relation gives rise to a morphism, only for immediately solving goals without variables. *)

Lemma reflexive_proper `{Reflexive A R} (x : A)
   : Proper R x.
Proof. firstorder. Qed.

Lemma proper_eq A (x : A) : Proper (@eq A) x.
Proof. intros. apply reflexive_proper. Qed.

Ltac proper_reflexive :=
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | _ => class_apply proper_eq || class_apply @reflexive_proper
  end.

Hint Extern 7 (@Proper _ _ _) => proper_reflexive : typeclass_instances.


(** When the relation on the domain is symmetric, we can
    inverse the relation on the codomain. Same for binary functions. *)

Lemma proper_sym_flip
 `(Symmetric A R1)`(Proper (A->B) (R1==>R2) f) :
 Proper (R1==>inverse R2) f.
Proof.
intros A R1 Sym B R2 f Hf.
intros x x' Hxx'. apply Hf, Sym, Hxx'.
Qed.

Lemma proper_sym_flip_2
 `(Symmetric A R1)`(Symmetric B R2)`(Proper (A->B->C) (R1==>R2==>R3) f) :
 Proper (R1==>R2==>inverse R3) f.
Proof.
intros A R1 Sym1 B R2 Sym2 C R3 f Hf.
intros x x' Hxx' y y' Hyy'. apply Hf; auto.
Qed.

(** When the relation on the domain is symmetric, a predicate is
  compatible with [iff] as soon as it is compatible with [impl].
  Same with a binary relation. *)

Lemma proper_sym_impl_iff `(Symmetric A R)`(Proper _ (R==>impl) f) :
 Proper (R==>iff) f.
Proof.
intros A R Sym f Hf x x' Hxx'. repeat red in Hf. split; eauto.
Qed.

Lemma proper_sym_impl_iff_2
 `(Symmetric A R)`(Symmetric B R')`(Proper _ (R==>R'==>impl) f) :
 Proper (R==>R'==>iff) f.
Proof.
intros A R Sym B R' Sym' f Hf x x' Hxx' y y' Hyy'.
repeat red in Hf. split; eauto.
Qed.

(** A [PartialOrder] is compatible with its underlying equivalence. *)

Instance PartialOrder_proper `(PartialOrder A eqA R) :
  Proper (eqA==>eqA==>iff) R.
Proof.
intros.
apply proper_sym_impl_iff_2; auto with *.
intros x x' Hx y y' Hy Hr.
transitivity x.
generalize (partial_order_equivalence x x'); compute; intuition.
transitivity y; auto.
generalize (partial_order_equivalence y y'); compute; intuition.
Qed.

(** From a [PartialOrder] to the corresponding [StrictOrder]:
     [lt = le /\ ~eq].
    If the order is total, we could also say [gt = ~le]. *)

Lemma PartialOrder_StrictOrder `(PartialOrder A eqA R) :
  StrictOrder (relation_conjunction R (complement eqA)).
Proof.
split; compute.
intros x (_,Hx). apply Hx, Equivalence_Reflexive.
intros x y z (Hxy,Hxy') (Hyz,Hyz'). split.
apply PreOrder_Transitive with y; assumption.
intro Hxz.
apply Hxy'.
apply partial_order_antisym; auto.
rewrite Hxz; auto.
Qed.

Hint Extern 4 (StrictOrder (relation_conjunction _ _)) => 
  class_apply PartialOrder_StrictOrder : typeclass_instances.

(** From a [StrictOrder] to the corresponding [PartialOrder]:
     [le = lt \/ eq].
    If the order is total, we could also say [ge = ~lt]. *)

Lemma StrictOrder_PreOrder
 `(Equivalence A eqA, StrictOrder A R, Proper _ (eqA==>eqA==>iff) R) :
 PreOrder (relation_disjunction R eqA).
Proof.
split.
intros x. right. reflexivity.
intros x y z [Hxy|Hxy] [Hyz|Hyz].
left. transitivity y; auto.
left. rewrite <- Hyz; auto.
left. rewrite Hxy; auto.
right. transitivity y; auto.
Qed.

Hint Extern 4 (PreOrder (relation_disjunction _ _)) => 
  class_apply StrictOrder_PreOrder : typeclass_instances.

Lemma StrictOrder_PartialOrder
  `(Equivalence A eqA, StrictOrder A R, Proper _ (eqA==>eqA==>iff) R) :
  PartialOrder eqA (relation_disjunction R eqA).
Proof.
intros. intros x y. compute. intuition.
elim (StrictOrder_Irreflexive x).
transitivity y; auto.
Qed.

Hint Extern 4 (PartialOrder _ (relation_disjunction _ _)) => 
  class_apply StrictOrder_PartialOrder : typeclass_instances.
