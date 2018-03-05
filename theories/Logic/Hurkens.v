(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                              Hurkens.v                               *)
(************************************************************************)

(** Exploiting Hurkens's paradox [[Hurkens95]] for system U- so as to
    derive various contradictory contexts.

    The file is divided into various sub-modules which all follow the
    same structure: a section introduces the contradictory hypotheses
    and a theorem named [paradox] concludes the module with a proof of
    [False].

    - The [Generic] module contains the actual Hurkens's paradox for a
      postulated shallow encoding of system U- in Coq. This is an
      adaptation by Arnaud Spiwack of a previous, more restricted
      implementation by Herman Geuvers. It is used to derive every
      other special cases of the paradox in this file.

    - The [NoRetractToImpredicativeUniverse] module contains a simple
      and effective formulation by Herman Geuvers [[Geuvers01]] of a
      result by Thierry Coquand [[Coquand90]]. It states that no
      impredicative sort can contain a type of which it is a
      retract. This result implies that Coq with classical logic
      stated in impredicative Set is inconsistent and that classical
      logic stated in Prop implies proof-irrelevance (see
      [ClassicalFacts.v])

    - The [NoRetractFromSmallPropositionToProp] module is a
      specialisation of the [NoRetractToImpredicativeUniverse] module
      to the case where the impredicative sort is [Prop].

    - The [NoRetractToModalProposition] module is a strengthening of
      the [NoRetractFromSmallPropositionToProp] module.  It shows that
      given a monadic modality (aka closure operator) [M], the type of
      modal propositions (i.e. such that [M A -> A]) cannot be a
      retract of a modal proposition. It is an example of use of the
      paradox where the universes of system U- are not mapped to
      universes of Coq.

    - The [NoRetractToNegativeProp] module is the specialisation of
      the [NoRetractFromSmallPropositionToProp] module where the
      modality is double-negation. This result implies that the
      principle of weak excluded middle ([forall A, ~~A\/~A]) implies
      a weak variant of proof irrelevance.

    - The [NoRetractFromTypeToProp] module proves that [Prop] cannot
      be a retract of a larger type.

    - The [TypeNeqSmallType] module proves that [Type] is different
      from any smaller type.

    - The [PropNeqType] module proves that [Prop] is different from
      any larger [Type]. It is an instance of the previous result.

    References:

    - [[Coquand90]] T. Coquand, "Metamathematical Investigations of a
      Calculus of Constructions", Proceedings of Logic in Computer
      Science (LICS'90), 1990.

    - [[Hurkens95]] A. J. Hurkens, "A simplification of Girard's paradox",
      Proceedings of the 2nd international conference Typed Lambda-Calculi
      and Applications (TLCA'95), 1995.

    - [[Geuvers01]] H. Geuvers, "Inconsistency of Classical Logic in Type
      Theory", 2001, revised 2007
      (see {{http://www.cs.ru.nl/~herman/PUBS/newnote.ps.gz}}).
*)


Set Universe Polymorphism.

(* begin show *)

(** * A modular proof of Hurkens's paradox. *)

(** It relies on an axiomatisation of a shallow embedding of system U-
    (i.e.  types of U- are interpreted by types of Coq). The
    universes are encoded in a style, due to Martin-Löf, where they
    are given by a set of names and a family [El:Name->Type] which
    interprets each name into a type. This allows the encoding of
    universe to be decoupled from Coq's universes. Dependent products
    and abstractions are similarly postulated rather than encoded as
    Coq's dependent products and abstractions. *)

Module Generic.

(* begin hide *)
(* Notations used in the proof. Hidden in coqdoc. *)

Reserved Notation "'∀₁' x : A , B" (at level 200, x ident, A at level 200,right associativity).
Reserved Notation "A '⟶₁' B" (at level 99, right associativity, B at level 200).
Reserved Notation "'λ₁' x , u" (at level 200, x ident, right associativity).
Reserved Notation "f '·₁' x" (at level 5, left associativity).
Reserved Notation "'∀₂' A , F" (at level 200, A ident, right associativity).
Reserved Notation "'λ₂' x , u" (at level 200, x ident, right associativity).
Reserved Notation "f '·₁' [ A ]" (at level 5, left associativity).
Reserved Notation "'∀₀' x : A , B" (at level 200, x ident, A at level 200,right associativity).
Reserved Notation "A '⟶₀' B" (at level 99, right associativity, B at level 200).
Reserved Notation "'λ₀' x , u" (at level 200, x ident, right associativity).
Reserved Notation "f '·₀' x" (at level 5, left associativity).
Reserved Notation "'∀₀¹' A : U , F" (at level 200, A ident, right associativity).
Reserved Notation "'λ₀¹' x , u" (at level 200, x ident, right associativity).
Reserved Notation "f '·₀' [ A ]" (at level 5, left associativity).

(* end hide *)

Section Paradox.

(** ** Axiomatisation of impredicative universes in a Martin-Löf style *)

(** System U- has two impredicative universes. In the proof of the
    paradox they are slightly asymmetric (in particular the reduction
    rules of the small universe are not needed).  Therefore, the
    axioms are duplicated allowing for a weaker requirement than the
    actual system U-. *)


(** *** Large universe *)
Variable U1 : Type.
Variable El1 : U1 -> Type.
(** **** Closure by small product *)
Variable Forall1 : forall u:U1, (El1 u -> U1) -> U1.
  Notation "'∀₁' x : A , B" := (Forall1 A (fun x => B)).
  Notation "A '⟶₁' B" := (Forall1 A (fun _ => B)).
Variable lam1 : forall u B, (forall x:El1 u, El1 (B x)) -> El1 (∀₁ x:u, B x).
  Notation "'λ₁' x , u" := (lam1 _ _ (fun x => u)).
Variable app1 : forall u B (f:El1 (Forall1 u B)) (x:El1 u), El1 (B x).
  Notation "f '·₁' x" := (app1 _ _ f x).
Variable beta1 : forall u B (f:forall x:El1 u, El1 (B x)) x,
                   (λ₁ y, f y) ·₁ x = f x.
(** **** Closure by large products *)
(** [U1] only needs to quantify over itself. *)
Variable ForallU1 : (U1->U1) -> U1.
  Notation "'∀₂' A , F" := (ForallU1 (fun A => F)).
Variable lamU1 : forall F, (forall A:U1, El1 (F A)) -> El1 (∀₂ A, F A).
  Notation "'λ₂' x , u" := (lamU1 _ (fun x => u)).
Variable appU1 : forall F (f:El1(∀₂ A,F A)) (A:U1), El1 (F A).
  Notation "f '·₁' [ A ]" := (appU1 _ f A).
Variable betaU1 : forall F (f:forall A:U1, El1 (F A)) A,
                    (λ₂ x, f x) ·₁ [ A ] = f A.

(** *** Small universe *)
(** The small universe is an element of the large one. *)
Variable u0 : U1.
Notation U0 := (El1 u0).
Variable El0 : U0 -> Type.
(** **** Closure by small product *)
(** [U0] does not need reduction rules *)
Variable Forall0 : forall u:U0, (El0 u -> U0) -> U0.
  Notation "'∀₀' x : A , B" := (Forall0 A (fun x => B)).
  Notation "A '⟶₀' B" := (Forall0 A (fun _ => B)).
Variable lam0 : forall u B, (forall x:El0 u, El0 (B x)) -> El0 (∀₀ x:u, B x).
  Notation "'λ₀' x , u" := (lam0 _ _ (fun x => u)).
Variable app0 : forall u B (f:El0 (Forall0 u B)) (x:El0 u), El0 (B x).
  Notation "f '·₀' x" := (app0 _ _ f x).
(** **** Closure by large products *)
Variable ForallU0 : forall u:U1, (El1 u->U0) -> U0.
  Notation "'∀₀¹' A : U , F" := (ForallU0 U (fun A => F)).
Variable lamU0 : forall U F, (forall A:El1 U, El0 (F A)) -> El0 (∀₀¹ A:U, F A).
  Notation "'λ₀¹' x , u" := (lamU0 _ _ (fun x => u)).
Variable appU0 : forall U F (f:El0(∀₀¹ A:U,F A)) (A:El1 U), El0 (F A).
  Notation "f '·₀' [ A ]" := (appU0 _ _ f A).

(** ** Automating the rewrite rules of our encoding. *)
Local Ltac simplify :=
  (* spiwack: ideally we could use [rewrite_strategy] here, but I am a tad
     scared of the idea of depending on setoid rewrite in such a simple
     file. *)
  (repeat rewrite ?beta1, ?betaU1);
  lazy beta.

Local Ltac simplify_in h :=
  (repeat rewrite ?beta1, ?betaU1 in h);
  lazy beta in h.


(** ** Hurkens's paradox. *)

(** An inhabitant of [U0] standing for [False]. *)
Variable F:U0.

(** *** Preliminary definitions *)

Definition V : U1 := ∀₂ A, ((A ⟶₁ u0) ⟶₁ A ⟶₁ u0) ⟶₁ A ⟶₁ u0.
Definition U : U1 := V ⟶₁ u0.

Definition sb (z:El1 V) : El1 V := λ₂ A, λ₁ r, λ₁ a, r ·₁ (z·₁[A]·₁r) ·₁ a.

Definition le (i:El1 (U⟶₁u0)) (x:El1 U) : U0 :=
  x ·₁ (λ₂ A, λ₁ r, λ₁ a, i ·₁ (λ₁ v, (sb v) ·₁ [A] ·₁ r ·₁ a)).
Definition le' : El1 ((U⟶₁u0) ⟶₁ U ⟶₁ u0) := λ₁ i, λ₁ x, le i x.
Definition induct (i:El1 (U⟶₁u0)) : U0 :=
  ∀₀¹ x:U, le i x ⟶₀ i ·₁ x.

Definition WF : El1 U := λ₁ z, (induct (z·₁[U] ·₁ le')).
Definition I (x:El1 U) : U0 :=
  (∀₀¹ i:U⟶₁u0, le i x ⟶₀ i ·₁ (λ₁ v, (sb v) ·₁ [U] ·₁ le' ·₁ x)) ⟶₀ F
.

(** *** Proof *)

Lemma Omega : El0 (∀₀¹ i:U⟶₁u0, induct i ⟶₀ i ·₁ WF).
Proof.
  refine (λ₀¹ i, λ₀ y, _).
  refine (y·₀[_]·₀_).
  unfold le,WF,induct. simplify.
  refine (λ₀¹ x, λ₀ h0, _). simplify.
  refine (y·₀[_]·₀_).
  unfold le. simplify.
  unfold sb at 1. simplify.
  unfold le' at 1. simplify.
  exact h0.
Qed.

Lemma lemma1 : El0 (induct (λ₁ u, I u)).
Proof.
  unfold induct.
  refine (λ₀¹ x, λ₀ p, _). simplify.
  refine (λ₀ q,_).
  assert (El0 (I (λ₁ v, (sb v)·₁[U]·₁le'·₁x))) as h.
  { generalize (q·₀[λ₁ u, I u]·₀p). simplify.
    intros q'.
    exact q'. }
  refine (h·₀_).
  refine (λ₀¹ i,_).
  refine (λ₀ h', _).
  generalize (q·₀[λ₁ y, i ·₁ (λ₁ v, (sb v)·₁[U] ·₁ le' ·₁ y)]). simplify.
  intros q'.
  refine (q'·₀_). clear q'.
  unfold le at 1 in h'. simplify_in h'.
  unfold sb at 1 in h'. simplify_in h'.
  unfold le' at 1 in h'. simplify_in h'.
  exact h'.
Qed.

Lemma lemma2 : El0 ((∀₀¹i:U⟶₁u0, induct i ⟶₀ i·₁WF) ⟶₀ F).
Proof.
  refine (λ₀ x, _).
  assert (El0 (I WF)) as h.
  { generalize (x·₀[λ₁ u, I u]·₀lemma1). simplify.
    intros q.
    exact q. }
  refine (h·₀_). clear h.
  refine (λ₀¹ i, λ₀ h0, _).
  generalize (x·₀[λ₁ y, i·₁(λ₁ v, (sb v)·₁[U]·₁le'·₁y)]). simplify.
  intros q.
  refine (q·₀_). clear q.
  unfold le in h0. simplify_in h0.
  unfold WF in h0. simplify_in h0.
  exact h0.
Qed.

Theorem paradox : El0 F.
Proof.
  exact (lemma2·₀Omega).
Qed.

End Paradox.

(** The [paradox] tactic can be called as a shortcut to use the paradox. *)
Ltac paradox h :=
  unshelve (refine ((fun h => _) (paradox _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ))).

End Generic.

(** * Impredicative universes are not retracts. *)

(** There can be no retract to an impredicative Coq universe from a
    smaller type. In this version of the proof, the impredicativity of
    the universe is postulated with a pair of functions from the
    universe to its type and back which commute with dependent product
    in an appropriate way. *)

Module NoRetractToImpredicativeUniverse.

Section Paradox.

Let      U2    := Type.
Let      U1:U2 := Type.
Variable U0:U1.

(** *** [U1] is impredicative *)
Variable u22u1 : U2 -> U1.
Hypothesis u22u1_unit   : forall (c:U2), c -> u22u1 c.
(** [u22u1_counit] and [u22u1_coherent] only apply to dependent
    product so that the equations happen in the smaller [U1] rather
    than [U2].  Indeed, it is not generally the case that one can
    project from a large universe to an impredicative universe and
    then get back the original type again. It would be too strong a
    hypothesis to require (in particular, it is not true of
    [Prop]). The formulation is reminiscent of the monadic
    characteristic of the projection from a large type to [Prop].*)
Hypothesis u22u1_counit : forall (F:U1->U1), u22u1 (forall A,F A) -> (forall A,F A).
Hypothesis u22u1_coherent : forall (F:U1 -> U1) (f:forall x:U1, F x) (x:U1), 
                              u22u1_counit _ (u22u1_unit _ f) x = f x.

(** *** [U0] is a retract of [U1] *)
Variable u02u1 : U0 -> U1.
Variable u12u0 : U1 -> U0.
Hypothesis u12u0_unit   : forall (b:U1), b -> u02u1 (u12u0 b).
Hypothesis u12u0_counit : forall (b:U1), u02u1 (u12u0 b) -> b.

(** ** Paradox *)

Theorem paradox : forall F:U1, F.
Proof.
  intros F.
  Generic.paradox h.
  (** Large universe *)
  + exact U1.
  + exact (fun X => X).
  + cbn. exact (fun u F => forall x:u, F x).
  + cbn. exact (fun _ _ x => x).
  + cbn. exact (fun _ _ x => x).

  + cbn. exact (fun F => u22u1 (forall x, F x)).
  + cbn. exact (fun _ x => u22u1_unit _ x).
  + cbn. exact (fun _ x => u22u1_counit _ x).
  (** Small universe *)
  + exact U0.
  (** The interpretation of the small universe is the image of
      [U0] in [U1]. *)
  + cbn. exact (fun X => u02u1 X).
  + cbn. exact (fun u F => u12u0 (forall x:(u02u1 u), u02u1 (F x))).
  + cbn. exact (fun u F => u12u0 (forall x:u, u02u1 (F x))).
  + cbn. exact (u12u0 F).
  + cbn in h.
    exact (u12u0_counit _ h).
  + cbn. easy.
  + cbn. intros **. now rewrite u22u1_coherent.
  + cbn. intros * x. exact (u12u0_unit _ x).
  + cbn. intros * x. exact (u12u0_counit _ x).
  + cbn. intros * x. exact (u12u0_unit _ x).
  + cbn. intros * x. exact (u12u0_counit _ x).
Qed.

End Paradox.

End NoRetractToImpredicativeUniverse.

(** * Modal fragments of [Prop] are not retracts *)

(** In presence of a a monadic modality on [Prop], we can define a
    subset of [Prop] of modal propositions which is also a complete
    Heyting algebra. These cannot be a retract of a modal
    proposition. This is a case where the universe in system U- are
    not encoded as Coq universes. *)

Module NoRetractToModalProposition.

(** ** Monadic modality *)

Section Paradox.

Variable M : Prop -> Prop.
Hypothesis incr : forall A B:Prop, (A->B) -> M A -> M B.

Lemma strength: forall A (P:A->Prop), M(forall x:A,P x) -> forall x:A,M(P x).
Proof.
  intros A P h x.
  eapply incr in h; eauto.
Qed.

(** ** The universe of modal propositions *)

Definition MProp := { P:Prop | M P -> P }.
Definition El : MProp -> Prop := @proj1_sig _ _.

Lemma modal : forall P:MProp, M(El P) -> El P.
Proof.
  intros [P m]. cbn.
  exact m.
Qed.

Definition Forall {A:Type} (P:A->MProp) : MProp.
Proof.
  unshelve (refine (exist _ _ _)).
  + exact (forall x:A, El (P x)).
  + intros h x.
    eapply strength in h.
    eauto using modal.
Defined.

(** ** Retract of the modal fragment of [Prop] in a small type *)

(** The retract is axiomatized using logical equivalence as the
    equality on propositions. *)

Variable bool : MProp.
Variable p2b : MProp -> El bool.
Variable b2p : El bool -> MProp.
Hypothesis p2p1 : forall A:MProp, El (b2p (p2b A)) -> El A.
Hypothesis p2p2 : forall A:MProp, El A -> El (b2p (p2b A)).

(** ** Paradox *)

Theorem paradox : forall B:MProp, El B.
Proof.
  intros B.
  Generic.paradox h.
  (** Large universe *)
  + exact MProp.
  + exact El.
  + exact (fun _ => Forall).
  + cbn. exact (fun _ _ f => f).
  + cbn. exact (fun _ _ f => f).
  + exact Forall.
  + cbn. exact (fun _ f => f).
  + cbn. exact (fun _ f => f).
  (** Small universe *)
  + exact bool.
  + exact (fun b => El (b2p b)).
  + cbn. exact (fun _ F => p2b (Forall (fun x => b2p (F x)))).
  + exact (fun _ F => p2b (Forall (fun x => b2p (F x)))).
  + apply p2b.
    exact B.
  + cbn in h. auto.
  + cbn. easy.
  + cbn. easy.
  + cbn. auto.
  + cbn. intros * f.
    apply p2p1 in f. cbn in f.
    exact f.
  + cbn. auto.
  + cbn. intros * f.
    apply p2p1 in f. cbn in f.
    exact f.
Qed.

End Paradox.

End NoRetractToModalProposition.

(** * The negative fragment of [Prop] is not a retract *)

(** The existence in the pure Calculus of Constructions of a retract
    from the negative fragment of [Prop] into a negative proposition
    is inconsistent. This is an instance of the previous result. *)

Module NoRetractToNegativeProp.

(** ** The universe of negative propositions. *)

Definition NProp := { P:Prop | ~~P -> P }.
Definition El : NProp -> Prop := @proj1_sig _ _.

Section Paradox.

(** ** Retract of the negative fragment of [Prop] in a small type *)

(** The retract is axiomatized using logical equivalence as the
    equality on propositions. *)

Variable bool : NProp.
Variable p2b : NProp -> El bool.
Variable b2p : El bool -> NProp.
Hypothesis p2p1 : forall A:NProp, El (b2p (p2b A)) -> El A.
Hypothesis p2p2 : forall A:NProp, El A -> El (b2p (p2b A)).

(** ** Paradox *)

Theorem paradox : forall B:NProp, El B.
Proof.
  intros B.
  unshelve (refine ((fun h => _) (NoRetractToModalProposition.paradox _ _ _ _ _ _ _ _))).
  + exact (fun P => ~~P).
  + exact bool.
  + exact p2b.
  + exact b2p.
  + exact B.
  + exact h.
  + cbn. auto.
  + cbn. auto.
  + cbn. auto.
Qed.

End Paradox.

End NoRetractToNegativeProp.

(** * Prop is not a retract *)

(** The existence in the pure Calculus of Constructions of a retract
    from [Prop] into a small type of [Prop] is inconsistent. This is a
    special case of the previous result. *)

Module NoRetractFromSmallPropositionToProp.

(** ** The universe of propositions. *)

Definition NProp := { P:Prop | P -> P}.
Definition El : NProp -> Prop := @proj1_sig _ _.

Section MParadox.

(** ** Retract of [Prop] in a small type, using the identity modality. *)

Variable bool : NProp.
Variable p2b : NProp -> El bool.
Variable b2p : El bool -> NProp.
Hypothesis p2p1 : forall A:NProp, El (b2p (p2b A)) -> El A.
Hypothesis p2p2 : forall A:NProp, El A -> El (b2p (p2b A)).

(** ** Paradox *)

Theorem mparadox : forall B:NProp, El B.
Proof.
  intros B.
  unshelve (refine ((fun h => _) (NoRetractToModalProposition.paradox _ _ _ _ _ _ _ _))).
  + exact (fun P => P).
  + exact bool.
  + exact p2b.
  + exact b2p.
  + exact B.
  + exact h.
  + cbn. auto.
  + cbn. auto.
  + cbn. auto.
Qed.

End MParadox.

Section Paradox.

(** ** Retract of [Prop] in a small type *)

(** The retract is axiomatized using logical equivalence as the
    equality on propositions. *)
Variable bool : Prop.
Variable p2b : Prop -> bool.
Variable b2p : bool -> Prop.
Hypothesis p2p1 : forall A:Prop, b2p (p2b A) -> A.
Hypothesis p2p2 : forall A:Prop, A -> b2p (p2b A).

(** ** Paradox *)

Theorem paradox : forall B:Prop, B.
Proof.
  intros B.
  unshelve (refine (mparadox (exist _ bool (fun x => x)) _ _ _ _
                   (exist _ B (fun x => x)))).
  + intros p. red. red. exact (p2b (El p)).
  + cbn. intros b. red. exists (b2p b). exact (fun x => x).
  + cbn. intros [A H]. cbn. apply p2p1.
  + cbn. intros [A H]. cbn. apply p2p2.
Qed.

End Paradox.

End NoRetractFromSmallPropositionToProp.


(** * Large universes are not retracts of [Prop]. *)

(** The existence in the Calculus of Constructions with universes of a
    retract from some [Type] universe into [Prop] is inconsistent. *)

(* Note: Assuming the context [down:Type->Prop; up:Prop->Type; forth:
      forall (A:Type), A -> up (down A); back: forall (A:Type), up
      (down A) -> A; H: forall (A:Type) (P:A->Type) (a:A),
      P (back A (forth A a)) -> P a] is probably enough.  *)

Module NoRetractFromTypeToProp.

Definition Type2 := Type.
Definition Type1 := Type : Type2.

Section Paradox.

(** ** Assumption of a retract from Type into Prop *)

Variable down : Type1 -> Prop.
Variable up : Prop -> Type1.
Hypothesis up_down : forall (A:Type1), up (down A) = A :> Type1.

(** ** Paradox *)

Theorem paradox : forall P:Prop, P.
Proof.
  intros P.
  Generic.paradox h.
  (** Large universe. *)
  + exact Type1.
  + exact (fun X => X).
  + cbn. exact (fun u F => forall x, F x).
  + cbn. exact (fun _ _ x => x).
  + cbn. exact (fun _ _ x => x).
  + exact (fun F => forall A:Prop, F(up A)).
  + cbn. exact (fun F f A => f (up A)).
  + cbn.
    intros F f A.
    specialize (f (down A)).
    rewrite up_down in f.
    exact f.
  + exact Prop.
  + cbn. exact (fun X => X).
  + cbn. exact (fun A P => forall x:A, P x).
  + cbn. exact (fun A P => forall x:A, P x).
  + cbn. exact P.
  + exact h.
  + cbn. easy.
  + cbn.
    intros F f A.
    destruct (up_down A). cbn.
    reflexivity.
  + cbn. exact (fun _ _ x => x).
  + cbn. exact (fun _ _ x => x).
  + cbn. exact (fun _ _ x => x).
  + cbn. exact (fun _ _ x => x).
Qed.

End Paradox.

End NoRetractFromTypeToProp.

(** * [A<>Type] *)

(** No Coq universe can be equal to one of its elements. *)

Module TypeNeqSmallType.

Unset Universe Polymorphism.

Section Paradox.

(** ** Universe [U] is equal to one of its elements. *)

Let U := Type.
Variable A:U.
Hypothesis h : U=A.

(** ** Universe [U] is a retract of [A] *)

(** The following context is actually sufficient for the paradox to
    hold. The hypothesis [h:U=A] is only used to define [down], [up]
    and [up_down]. *)

Let down (X:U) : A := @eq_rect _ _ (fun X => X) X _ h.
Let up   (X:A) : U := @eq_rect_r _ _ (fun X => X) X _ h.

Lemma up_down : forall (X:U), up (down X) = X.
Proof.
  unfold up,down.
  rewrite <- h.
  reflexivity.
Qed.

Theorem paradox : False.
Proof.
  Generic.paradox p.
  (** Large universe *)
  + exact U.
  + exact (fun X=>X).
  + cbn. exact (fun X F => forall x:X, F x).
  + cbn. exact (fun _ _ x => x).
  + cbn. exact (fun _ _ x => x).
  + exact (fun F => forall x:A, F (up x)).
  + cbn. exact (fun _ f => fun x:A => f (up x)).
  + cbn. intros * f X.
    specialize (f (down X)).
    rewrite up_down in f.
    exact f.
  (** Small universe *)
  + exact A.
  (** The interpretation of [A] as a universe is [U]. *)
  + cbn. exact up.
  + cbn. exact (fun _ F => down (forall x, up (F x))).
  + cbn. exact (fun _ F => down (forall x, up (F x))).
  + cbn. exact (down False).
  + rewrite up_down in p.
    exact p.
  + cbn. easy.
  + cbn. intros ? f X.
    destruct (up_down X). cbn.
    reflexivity.
  + cbn. intros ? ? f.
    rewrite up_down.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down in f.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down in f.
    exact f.
Qed.

End Paradox.

End TypeNeqSmallType.

(** * [Prop<>Type]. *)

(** Special case of [TypeNeqSmallType]. *)

Module PropNeqType.

Theorem paradox : Prop <> Type.
Proof.
  intros h.
  unshelve (refine (TypeNeqSmallType.paradox _ _)).
  + exact Prop.
  + easy.
Qed.

End PropNeqType.

(* end show *)
