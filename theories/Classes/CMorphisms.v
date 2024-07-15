(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Typeclass-based morphism definition and standard, minimal instances

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Stdlib.Program.Basics.
Require Import Stdlib.Program.Tactics.
Require Export Stdlib.Classes.CRelationClasses.

Generalizable Variables A eqA B C D R RA RB RC m f x y.
Local Obligation Tactic := try solve [ simpl_crelation ].

Local Arguments transitivity {A R Transitive x} y {z}.

Set Universe Polymorphism.

(** * Morphisms.

   We now turn to the definition of [Proper] and declare standard instances.
   These will be used by the [setoid_rewrite] tactic later. *)

(** A morphism for a relation [R] is a proper element of the relation.
   The relation [R] will be instantiated by [respectful] and [A] by an arrow
   type for usual morphisms. *)
Section Proper.
  Context {A : Type}.

  Class Proper (R : crelation A) (m : A) :=
    proper_prf : R m m.

  (** Every element in the carrier of a reflexive relation is a morphism
   for this relation.  We use a proxy class for this case which is used
   internally to discharge reflexivity constraints.  The [Reflexive]
   instance will almost always be used, but it won't apply in general to
   any kind of [Proper (A -> B) _ _] goal, making proof-search much
   slower. A cleaner solution would be to be able to set different
   priorities in different hint bases and select a particular hint
   database for resolution of a type class constraint. *)

  Class ProperProxy (R : crelation A) (m : A) :=
    proper_proxy : R m m.

  Lemma eq_proper_proxy (x : A) : ProperProxy (@eq A) x.
  Proof. firstorder. Qed.
  
  Lemma reflexive_proper_proxy `(Reflexive A R) (x : A) : ProperProxy R x.
  Proof. firstorder. Qed.

  Lemma proper_proper_proxy x `(Proper R x) : ProperProxy R x.
  Proof. firstorder. Qed.

  (** Respectful morphisms. *)
  
  (** The fully dependent version, not used yet. *)
  
  Definition respectful_hetero
  (A B : Type)
  (C : A -> Type) (D : B -> Type)
  (R : A -> B -> Type)
  (R' : forall (x : A) (y : B), C x -> D y -> Type) :
    (forall x : A, C x) -> (forall x : B, D x) -> Type :=
    fun f g => forall x y, R x y -> R' x y (f x) (g y).

  (** The non-dependent version is an instance where we forget dependencies. *)
  
  Definition respectful {B} (R : crelation A) (R' : crelation B) : crelation (A -> B) :=
    Eval compute in @respectful_hetero A A (fun _ => B) (fun _ => B) R (fun _ _ => R').
End Proper.

(** We favor the use of Leibniz equality or a declared reflexive crelation 
  when resolving [ProperProxy], otherwise, if the crelation is given (not an evar),
  we fall back to [Proper]. *)
#[global]
Hint Extern 1 (ProperProxy _ _) => 
  class_apply @eq_proper_proxy || class_apply @reflexive_proper_proxy : typeclass_instances.

#[global]
Hint Extern 2 (ProperProxy ?R _) => 
  not_evar R; class_apply @proper_proper_proxy : typeclass_instances.

(** Notations reminiscent of the old syntax for declaring morphisms. *)
Declare Scope signatureT_scope.
Delimit Scope signatureT_scope with signatureT.

Module ProperNotations.

  Notation " R ++> R' " := (@respectful _ _ (R%signatureT) (R'%signatureT))
    (right associativity, at level 55) : signatureT_scope.

  Notation " R ==> R' " := (@respectful _ _ (R%signatureT) (R'%signatureT))
    (right associativity, at level 55) : signatureT_scope.

  Notation " R --> R' " := (@respectful _ _ (flip (R%signatureT)) (R'%signatureT))
    (right associativity, at level 55) : signatureT_scope.

End ProperNotations.

Arguments Proper {A}%_type R%_signatureT m.
Arguments respectful {A B}%_type (R R')%_signatureT _ _.

Export ProperNotations.

Local Open Scope signatureT_scope.

(** [solve_proper] try to solve the goal [Proper (?==> ... ==>?) f]
    by repeated introductions and setoid rewrites. It should work
    fine when [f] is a combination of already known morphisms and
    quantifiers. *)

Ltac solve_respectful t :=
 match goal with
   | |- respectful _ _ _ _ =>
     let H := fresh "H" in
     intros ? ? H; solve_respectful ltac:(setoid_rewrite H; t)
   | _ => t; reflexivity
 end.

Ltac solve_proper := unfold Proper; solve_respectful ltac:(idtac).

(** [f_equiv] is a clone of [f_equal] that handles setoid equivalences.
    For example, if we know that [f] is a morphism for [E1==>E2==>E],
    then the goal [E (f x y) (f x' y')] will be transformed by [f_equiv]
    into the subgoals [E1 x x'] and [E2 y y'].
*)

Ltac f_equiv :=
 match goal with
  | |- ?R (?f ?x) (?f' _) =>
    let T := type of x in
    let Rx := fresh "R" in
    evar (Rx : crelation T);
    let H := fresh in
    assert (H : (Rx==>R)%signatureT f f');
    unfold Rx in *; clear Rx; [ f_equiv | apply H; clear H; try reflexivity ]
  | |- ?R ?f ?f' =>
    solve [change (Proper R f); eauto with typeclass_instances | reflexivity ]
  | _ => idtac
 end.

Section Relations.
  Context {A : Type}. 

  (** [forall_def] reifies the dependent product as a definition. *)
  
  Definition forall_def (P : A -> Type) : Type := forall x : A, P x.
  
  (** Dependent pointwise lifting of a crelation on the range. *)
  
  Definition forall_relation (P : A -> Type)
             (sig : forall a, crelation (P a)) : crelation (forall x, P x) :=
    fun f g => forall a, sig a (f a) (g a).

  (** Non-dependent pointwise lifting *)
  Definition pointwise_relation {B} (R : crelation B) : crelation (A -> B) :=
    fun f g => forall a, R (f a) (g a).

  Lemma pointwise_pointwise {B} (R : crelation B) :
    relation_equivalence (pointwise_relation R) (@eq A ==> R).
  Proof.
    intros. split.
    - simpl_crelation.
    - firstorder.
  Qed.
  
  (** Subcrelations induce a morphism on the identity. *)
  
  Global Instance subrelation_id_proper `(subrelation A RA RA') : Proper (RA ==> RA') id.
  Proof. firstorder. Qed.

  (** The subrelation property goes through products as usual. *)
  
  Lemma subrelation_respectful `(subl : subrelation A RA' RA, subr : subrelation B RB RB') :
    subrelation (RA ==> RB) (RA' ==> RB').
  Proof. simpl_crelation. Qed.

  (** And of course it is reflexive. *)
  
  Lemma subrelation_refl R : @subrelation A R R.
  Proof. simpl_crelation. Qed.

  (** [Proper] is itself a covariant morphism for [subrelation].
   We use an unconvertible premise to avoid looping.
   *)
  
  Lemma subrelation_proper `(mor : Proper A R' m) 
        `(unc : Unconvertible (crelation A) R R')
        `(sub : subrelation A R' R) : Proper R m.
  Proof.
    intros. apply sub. apply mor.
  Qed.

  Global Instance proper_subrelation_proper_arrow :
    Proper (subrelation ++> eq ==> arrow) (@Proper A).
  Proof. reduce. subst. firstorder. Qed.

  Global Instance pointwise_subrelation `(sub : subrelation B R R') :
    subrelation (pointwise_relation R) (pointwise_relation R') | 4.
  Proof. reduce. unfold pointwise_relation in *. apply sub. auto. Qed.
  
  (** For dependent function types. *)
  Lemma forall_subrelation (P : A -> Type) (R S : forall x : A, crelation (P x)) :
    (forall a, subrelation (R a) (S a)) -> 
    subrelation (forall_relation P R) (forall_relation P S).
  Proof. reduce. firstorder. Qed.
End Relations.
Global Typeclasses Opaque respectful pointwise_relation forall_relation.
Arguments forall_relation {A P}%_type sig%_signatureT _ _.
Arguments pointwise_relation A%_type {B}%_type R%_signatureT _ _.
  
#[global]
Hint Unfold Reflexive : core.
#[global]
Hint Unfold Symmetric : core.
#[global]
Hint Unfold Transitive : core.

(** Resolution with subrelation: favor decomposing products over applying reflexivity
  for unconstrained goals. *)
Ltac subrelation_tac T U :=
  (is_ground T ; is_ground U ; class_apply @subrelation_refl) ||
    class_apply @subrelation_respectful || class_apply @subrelation_refl.

#[global]
Hint Extern 3 (@subrelation _ ?T ?U) => subrelation_tac T U : typeclass_instances.

CoInductive apply_subrelation : Prop := do_subrelation.

Ltac proper_subrelation :=
  match goal with
    [ H : apply_subrelation |- _ ] => clear H ; class_apply @subrelation_proper
  end.

#[global]
Hint Extern 5 (@Proper _ ?H _) => proper_subrelation : typeclass_instances.

(** Essential subrelation instances for [iff], [impl] and [pointwise_relation]. *)

#[global]
Instance iff_impl_subrelation : subrelation iff impl | 2.
Proof. firstorder. Qed.

#[global]
Instance iff_flip_impl_subrelation : subrelation iff (flip impl) | 2.
Proof. firstorder. Qed.

(** Essential subrelation instances for [iffT] and [arrow]. *)

#[global]
Instance iffT_arrow_subrelation : subrelation iffT arrow | 2.
Proof. firstorder. Qed.

#[global]
Instance iffT_flip_arrow_subrelation : subrelation iffT (flip arrow) | 2.
Proof. firstorder. Qed.

(** We use an extern hint to help unification. *)

#[global]
Hint Extern 4 (subrelation (@forall_relation ?A ?B ?R) (@forall_relation _ _ ?S)) =>
  apply (@forall_subrelation A B R S) ; intro : typeclass_instances.

Section GenericInstances.
  (* Share universes *)
  Implicit Types A B C : Type.

  (** We can build a PER on the Coq function space if we have PERs on the domain and
   codomain. *)
  
  Program Instance respectful_per `(PER A R, PER B R') : PER (R ==> R').

  Next Obligation.
  Proof with auto.
    intros A R H B R' H0 x y z X X0 x0 y0 X1.
    assert(R x0 x0).
    - eapply transitivity with y0... now apply symmetry.
    - eapply transitivity with (y x0)...
  Qed.

  Unset Strict Universe Declaration.
  
  (** The complement of a crelation conserves its proper elements. *)
 
  (** The [flip] too, actually the [flip] instance is a bit more general. *)
  Program Definition flip_proper
          `(mor : Proper (A -> B -> C) (RA ==> RB ==> RC) f) :
    Proper (RB ==> RA ==> RC) (flip f) := _.
  
  Next Obligation.
  Proof.
    intros A B C RA RB RC f mor x y X x0 y0 X0.
    apply mor ; auto.
  Qed.


  (** Every Transitive crelation gives rise to a binary morphism on [impl],
   contravariant in the first argument, covariant in the second. *)
  
  Global Program 
  Instance trans_contra_co_type_morphism
    `(Transitive A R) : Proper (R --> R ++> arrow) R.
  
  Next Obligation.
  Proof with auto.
    intros A R H x y X x0 y0 X0 X1.
    apply transitivity with x...
    apply transitivity with x0...
  Qed.

  (** Proper declarations for partial applications. *)

  Global Program 
  Instance trans_contra_inv_impl_type_morphism
  `(Transitive A R) {x} : Proper (R --> flip arrow) (R x) | 3.

  Next Obligation.
  Proof with auto.
    intros A R H x x0 y X X0.
    apply transitivity with y...
  Qed.

  Global Program 
  Instance trans_co_impl_type_morphism
    `(Transitive A R) {x} : Proper (R ++> arrow) (R x) | 3.

  Next Obligation.
  Proof with auto.
    intros A R H x x0 y X X0.
    apply transitivity with x0...
  Qed.

  Global Program 
  Instance trans_sym_co_inv_impl_type_morphism
    `(PER A R) {x} : Proper (R ++> flip arrow) (R x) | 3.

  Next Obligation.
  Proof with auto.
    intros A R H x x0 y X X0.
    apply transitivity with y... apply symmetry...
  Qed.

  Global Program Instance trans_sym_contra_arrow_morphism
    `(PER A R) {x} : Proper (R --> arrow) (R x) | 3.

  Next Obligation.
  Proof with auto.
    intros A R H x x0 y X X0.
    apply transitivity with x0... apply symmetry...
  Qed.

  Global Program Instance per_partial_app_type_morphism
  `(PER A R) {x} : Proper (R ==> iffT) (R x) | 2.

  Next Obligation.
  Proof with auto.
    intros A R H x x0 y X.
    split.
    - intros ; apply transitivity with x0...
    - intros.
      apply transitivity with y...
      apply symmetry...
  Qed.

  (** Every Transitive crelation induces a morphism by "pushing" an [R x y] on the left of an [R x z] proof to get an [R y z] goal. *)

  Global Program 
  Instance trans_co_eq_inv_arrow_morphism
  `(Transitive A R) : Proper (R ==> (@eq A) ==> flip arrow) R | 2.

  Next Obligation.
  Proof with auto.
    intros A R H x y X y0 y1 e X0; destruct e.
    apply transitivity with y...
  Qed.

  (** Every Symmetric and Transitive crelation gives rise to an equivariant morphism. *)

  Global Program 
  Instance PER_type_morphism `(PER A R) : Proper (R ==> R ==> iffT) R | 1.

  Next Obligation.
  Proof with auto.
    intros A R H x y X x0 y0 X0.
    split ; intros.
    - apply transitivity with x0...
      apply transitivity with x... apply symmetry...

    - apply transitivity with y... apply transitivity with y0...
      apply symmetry...
  Qed.

  Lemma symmetric_equiv_flip `(Symmetric A R) : relation_equivalence R (flip R).
  Proof. firstorder. Qed.

  Global Program Instance compose_proper A B C RA RB RC :
    Proper ((RB ==> RC) ==> (RA ==> RB) ==> (RA ==> RC)) (@compose A B C).

  Next Obligation.
  Proof.
    simpl_crelation.
    unfold compose. firstorder. 
  Qed.

  (** Coq functions are morphisms for Leibniz equality,
     applied only if really needed. *)

  Global Instance reflexive_eq_dom_reflexive `(Reflexive B R') {A} :
    Reflexive (@Logic.eq A ==> R').
  Proof. simpl_crelation. Qed.

  (** [respectful] is a morphism for crelation equivalence . *)

  Global Instance respectful_morphism {A B} :
    Proper (relation_equivalence ++> relation_equivalence ++> relation_equivalence) 
           (@respectful A B).
  Proof. 
    intros R R' HRR' S S' HSS' f g.
    unfold respectful , relation_equivalence in *; simpl in *.
    split ; intros H x y Hxy.
    - apply (fst (HSS' _ _)). apply H. now apply (snd (HRR' _ _)).
    - apply (snd (HSS' _ _)). apply H. now apply (fst (HRR' _ _)).
  Qed.

  (** [R] is Reflexive, hence we can build the needed proof. *)

  Lemma Reflexive_partial_app_morphism `(Proper (A -> B) (R ==> R') m, ProperProxy A R x) :
    Proper R' (m x).
  Proof. simpl_crelation. Qed.
  
  Class Params {A} (of : A) (arity : nat).
    
  Lemma flip_respectful {A B} (R : crelation A) (R' : crelation B) :
    relation_equivalence (flip (R ==> R')) (flip R ==> flip R').
  Proof.
    intros.
    unfold flip, respectful.
    split ; intros ; intuition.
  Qed.

  
  (** Treating flip: can't make them direct instances as we
   need at least a [flip] present in the goal. *)
  
  Lemma flip1 `(subrelation A R' R) : subrelation (flip (flip R')) R.
  Proof. firstorder. Qed.
  
  Lemma flip2 `(subrelation A R R') : subrelation R (flip (flip R')).
  Proof. firstorder. Qed.
  
  (** That's if and only if *)
  
  Lemma eq_subrelation `(Reflexive A R) : subrelation (@eq A) R.
  Proof. simpl_crelation. Qed.

  (** Once we have normalized, we will apply this instance to simplify the problem. *)
  
  Definition proper_flip_proper `(mor : Proper A R m) : Proper (flip R) m := mor.
  
  (** Every reflexive crelation gives rise to a morphism, 
  only for immediately solving goals without variables. *)
  
  Lemma reflexive_proper `{Reflexive A R} (x : A) : Proper R x.
  Proof. firstorder. Qed.
  
  Lemma proper_eq {A} (x : A) : Proper (@eq A) x.
  Proof. intros. apply reflexive_proper. Qed.
  
End GenericInstances.

Class PartialApplication.

CoInductive normalization_done : Prop := did_normalization.

Ltac partial_application_tactic :=
  let rec do_partial_apps H m cont := 
    match m with
      | ?m' ?x => class_apply @Reflexive_partial_app_morphism ; 
        [(do_partial_apps H m' ltac:(idtac))|clear H]
      | _ => cont
    end
  in
  let rec do_partial H ar m := 
    match ar with
      | 0%nat => do_partial_apps H m ltac:(fail 1)
      | S ?n' =>
        match m with
          ?m' ?x => do_partial H n' m'
        end
    end
  in
  let params m sk fk :=
    (let m' := fresh in head_of_constr m' m ;
     let n := fresh in evar (n:nat) ;
     let v := eval compute in n in clear n ;
      let H := fresh in
        assert(H:Params m' v) by typeclasses eauto ;
          let v' := eval compute in v in subst m';
            (sk H v' || fail 1))
    || fk
  in
  let on_morphism m cont :=
    params m ltac:(fun H n => do_partial H n m)
      ltac:(cont)
  in
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | [ _ : @Params _ _ _ |- _ ] => fail 1
    | [ |- @Proper ?T _ (?m ?x) ] =>
      match goal with
        | [ H : PartialApplication |- _ ] =>
          class_apply @Reflexive_partial_app_morphism; [|clear H]
        | _ => on_morphism (m x)
          ltac:(class_apply @Reflexive_partial_app_morphism)
      end
  end.

(** Bootstrap !!! *)

#[global]
Instance proper_proper {A} : Proper (relation_equivalence ==> eq ==> iffT) (@Proper A).
Proof.
  intros R R' HRR' x y <-. red in HRR'.
  split ; red ; intros. 
  - now apply (fst (HRR' _ _)).
  - now apply (snd (HRR' _ _)).
Qed.

Ltac proper_reflexive :=
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | _ => class_apply proper_eq || class_apply @reflexive_proper
  end.


#[global]
Hint Extern 1 (subrelation (flip _) _) => class_apply @flip1 : typeclass_instances.
#[global]
Hint Extern 1 (subrelation _ (flip _)) => class_apply @flip2 : typeclass_instances.

(* Hint Extern 1 (Proper _ (complement _)) => apply @complement_proper  *)
(*   : typeclass_instances. *)
#[global]
Hint Extern 1 (Proper _ (flip _)) => apply @flip_proper 
  : typeclass_instances.
#[global]
Hint Extern 2 (@Proper _ (flip _) _) => class_apply @proper_flip_proper 
  : typeclass_instances.
#[global]
Hint Extern 4 (@Proper _ _ _) => partial_application_tactic 
  : typeclass_instances.
#[global]
Hint Extern 7 (@Proper _ _ _) => proper_reflexive 
  : typeclass_instances.

(** Special-purpose class to do normalization of signatures w.r.t. flip. *)

Section Normalize.
  Context (A : Type).

  Class Normalizes (m : crelation A) (m' : crelation A) :=
    normalizes : relation_equivalence m m'.
  
  (** Current strategy: add [flip] everywhere and reduce using [subrelation]
   afterwards. *)

  Lemma proper_normalizes_proper `(Normalizes R0 R1, Proper A R1 m) : Proper R0 m.
  Proof.
    apply (_ : Normalizes R0 R1). assumption.
  Qed.

  Lemma flip_atom R : Normalizes R (flip (flip R)).
  Proof.
    firstorder.
  Qed.

End Normalize.

Lemma flip_arrow `(NA : Normalizes A R (flip R'''), NB : Normalizes B R' (flip R'')) :
  Normalizes (A -> B) (R ==> R') (flip (R''' ==> R'')%signatureT).
Proof. 
  unfold Normalizes in *. intros.
  eapply transitivity; [|eapply symmetry, flip_respectful].
  now apply respectful_morphism.
Qed.

Ltac normalizes :=
  match goal with
    | [ |- Normalizes _ (respectful _ _) _ ] => class_apply @flip_arrow
    | _ => class_apply @flip_atom
  end.

Ltac proper_normalization :=
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | [ _ : apply_subrelation |- @Proper _ ?R _ ] => 
      let H := fresh "H" in
      set(H:=did_normalization) ; class_apply @proper_normalizes_proper
  end.

#[global]
Hint Extern 1 (Normalizes _ _ _) => normalizes : typeclass_instances.
#[global]
Hint Extern 6 (@Proper _ _ _) => proper_normalization 
  : typeclass_instances.

(** When the crelation on the domain is symmetric, we can
    flip the crelation on the codomain. Same for binary functions. *)

Lemma proper_sym_flip :
 forall `(Symmetric A R1)`(Proper (A->B) (R1==>R2) f),
 Proper (R1==>flip R2) f.
Proof.
intros A R1 Sym B R2 f Hf.
intros x x' Hxx'. apply Hf, Sym, Hxx'.
Qed.

Lemma proper_sym_flip_2 :
 forall `(Symmetric A R1)`(Symmetric B R2)`(Proper (A->B->C) (R1==>R2==>R3) f),
 Proper (R1==>R2==>flip R3) f.
Proof.
intros A R1 Sym1 B R2 Sym2 C R3 f Hf.
intros x x' Hxx' y y' Hyy'. apply Hf; auto.
Qed.

(** When the crelation on the domain is symmetric, a predicate is
  compatible with [iff] as soon as it is compatible with [impl].
  Same with a binary crelation. *)

Lemma proper_sym_impl_iff : forall `(Symmetric A R)`(Proper _ (R==>impl) f),
 Proper (R==>iff) f.
Proof.
intros A R Sym f Hf x x' Hxx'. repeat red in Hf. split; eauto.
Qed.

Lemma proper_sym_arrow_iffT : forall `(Symmetric A R)`(Proper _ (R==>arrow) f),
 Proper (R==>iffT) f.
Proof.
intros A R Sym f Hf x x' Hxx'. repeat red in Hf. split; eauto.
Qed.

Lemma proper_sym_impl_iff_2 :
 forall `(Symmetric A R)`(Symmetric B R')`(Proper _ (R==>R'==>impl) f),
 Proper (R==>R'==>iff) f.
Proof.
intros A R Sym B R' Sym' f Hf x x' Hxx' y y' Hyy'.
repeat red in Hf. split; eauto.
Qed.

Lemma proper_sym_arrow_iffT_2 :
 forall `(Symmetric A R)`(Symmetric B R')`(Proper _ (R==>R'==>arrow) f),
 Proper (R==>R'==>iffT) f.
Proof.
intros A R Sym B R' Sym' f Hf x x' Hxx' y y' Hyy'.
repeat red in Hf. split; eauto.
Qed.

(** A [PartialOrder] is compatible with its underlying equivalence. *)
Require Import Relation_Definitions.

#[global]
Instance PartialOrder_proper_type `(PartialOrder A eqA R) :
  Proper (eqA==>eqA==>iffT) R.
Proof.
intros.
apply proper_sym_arrow_iffT_2. 1-2: typeclasses eauto.
intros x x' Hx y y' Hy Hr.
apply transitivity with x.
- generalize (partial_order_equivalence x x'); compute; intuition.
- apply transitivity with y; auto.
  generalize (partial_order_equivalence y y'); compute; intuition.
Qed.

(** From a [PartialOrder] to the corresponding [StrictOrder]:
     [lt = le /\ ~eq].
    If the order is total, we could also say [gt = ~le]. *)

Lemma PartialOrder_StrictOrder `(PartialOrder A eqA R) :
  StrictOrder (relation_conjunction R (complement eqA)).
Proof.
split; compute.
- intros x (_,Hx). apply Hx, Equivalence_Reflexive.
- intros x y z (Hxy,Hxy') (Hyz,Hyz'). split.
  + apply PreOrder_Transitive with y; assumption.
  + intro Hxz.
    apply Hxy'.
    apply partial_order_antisym; auto.
    apply transitivity with z; [assumption|].
    now apply H.
Qed.

(** From a [StrictOrder] to the corresponding [PartialOrder]:
     [le = lt \/ eq].
    If the order is total, we could also say [ge = ~lt]. *)

Lemma StrictOrder_PreOrder
 `(Equivalence A eqA, StrictOrder A R, Proper _ (eqA==>eqA==>iffT) R) :
 PreOrder (relation_disjunction R eqA).
Proof.
split.
- intros x. right. apply reflexivity.
- intros x y z [Hxy|Hxy] [Hyz|Hyz].
  + left. apply transitivity with y; auto.
  + left. eapply H1; try eassumption. apply reflexivity.
    now apply symmetry.
  + left. eapply H1; [eassumption|apply reflexivity|eassumption].
  + right. apply transitivity with y; auto.
Qed.

#[global]
Hint Extern 4 (PreOrder (relation_disjunction _ _)) => 
  class_apply StrictOrder_PreOrder : typeclass_instances.

Lemma StrictOrder_PartialOrder
  `(Equivalence A eqA, StrictOrder A R, Proper _ (eqA==>eqA==>iffT) R) :
  PartialOrder eqA (relation_disjunction R eqA).
Proof.
intros. intros x y. compute. intuition auto.
- right; now apply symmetry.
- elim (StrictOrder_Irreflexive x).
  eapply transitivity with y; eauto.
- now apply symmetry.
Qed.

#[global]
Hint Extern 4 (StrictOrder (relation_conjunction _ _)) => 
  class_apply PartialOrder_StrictOrder : typeclass_instances.

#[global]
Hint Extern 4 (PartialOrder _ (relation_disjunction _ _)) => 
  class_apply StrictOrder_PartialOrder : typeclass_instances.

(* Register bindings for the generalized rewriting tactic *)

Register forall_relation as rewrite.type.forall_relation.
Register pointwise_relation as rewrite.type.pointwise_relation.
Register respectful as rewrite.type.respectful.
Register forall_def as rewrite.type.forall_def.
Register do_subrelation as rewrite.type.do_subrelation.
Register apply_subrelation as rewrite.type.apply_subrelation.
Register Proper as rewrite.type.Proper.
Register ProperProxy as rewrite.type.ProperProxy.
