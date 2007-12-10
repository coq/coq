(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export Relation_Definitions.

Set Implicit Arguments.

(** * Definitions of [Relation_Class] and n-ary [Morphism_Theory] *)

(* X will be used to distinguish covariant arguments whose type is an   *)
(* Asymmetric* relation from contravariant arguments of the same type *)
Inductive X_Relation_Class (X: Type) : Type :=
   SymmetricReflexive :
     forall A Aeq, symmetric A Aeq -> reflexive _ Aeq -> X_Relation_Class X
 | AsymmetricReflexive : X -> forall A Aeq, reflexive A Aeq -> X_Relation_Class X
 | SymmetricAreflexive : forall A Aeq, symmetric A Aeq -> X_Relation_Class X
 | AsymmetricAreflexive : X -> forall A (Aeq : relation A), X_Relation_Class X
 | Leibniz : Type -> X_Relation_Class X.

Inductive variance : Set :=
   Covariant
 | Contravariant.

Definition Argument_Class := X_Relation_Class variance.
Definition Relation_Class := X_Relation_Class unit.

Inductive Reflexive_Relation_Class : Type :=
   RSymmetric :
     forall A Aeq, symmetric A Aeq -> reflexive _ Aeq -> Reflexive_Relation_Class
 | RAsymmetric :
     forall A Aeq, reflexive A Aeq -> Reflexive_Relation_Class
 | RLeibniz : Type -> Reflexive_Relation_Class.

Inductive Areflexive_Relation_Class  : Type :=
 | ASymmetric : forall A Aeq, symmetric A Aeq -> Areflexive_Relation_Class
 | AAsymmetric : forall A (Aeq : relation A), Areflexive_Relation_Class.

Implicit Type Hole Out: Relation_Class.

Definition relation_class_of_argument_class : Argument_Class -> Relation_Class.
  destruct 1.
  exact (SymmetricReflexive _ s r).
  exact (AsymmetricReflexive tt r).
  exact (SymmetricAreflexive _ s).
  exact (AsymmetricAreflexive tt Aeq).
  exact (Leibniz _ T).
Defined.

Definition carrier_of_relation_class : forall X, X_Relation_Class X -> Type.
  destruct 1.
  exact A.
  exact A.
  exact A.
  exact A.
  exact T.
Defined.

Definition relation_of_relation_class :
  forall X R, @carrier_of_relation_class X R -> carrier_of_relation_class R -> Prop.
  destruct R.
  exact Aeq.
  exact Aeq.
  exact Aeq.
  exact Aeq.
  exact (@eq T).
Defined.

Lemma about_carrier_of_relation_class_and_relation_class_of_argument_class :
  forall R,
    carrier_of_relation_class (relation_class_of_argument_class R) =
    carrier_of_relation_class R.
  destruct R; reflexivity.
Defined.

Inductive nelistT (A : Type) : Type :=
   singl : A -> nelistT A
 | necons : A -> nelistT A -> nelistT A.

Definition Arguments := nelistT Argument_Class.

Implicit Type In: Arguments.

Definition function_type_of_morphism_signature :
  Arguments -> Relation_Class -> Type.
  intros In Out.
  induction In.
    exact (carrier_of_relation_class a -> carrier_of_relation_class Out).
    exact (carrier_of_relation_class a -> IHIn).
Defined. 

Definition make_compatibility_goal_aux:
  forall In Out
    (f g: function_type_of_morphism_signature In Out), Prop.
  intros; induction In; simpl in f, g.
    induction a; simpl in f, g.
      exact (forall x1 x2, Aeq x1 x2 -> relation_of_relation_class Out (f x1) (g x2)).
      destruct x.
        exact (forall x1 x2, Aeq x1 x2 -> relation_of_relation_class Out (f x1) (g x2)).
        exact (forall x1 x2, Aeq x2 x1 -> relation_of_relation_class Out (f x1) (g x2)).
      exact (forall x1 x2, Aeq x1 x2 -> relation_of_relation_class Out (f x1) (g x2)).
      destruct x.
        exact (forall x1 x2, Aeq x1 x2 -> relation_of_relation_class Out (f x1) (g x2)).
        exact (forall x1 x2, Aeq x2 x1 -> relation_of_relation_class Out (f x1) (g x2)).
      exact (forall x, relation_of_relation_class Out (f x) (g x)).
  induction a; simpl in f, g.
    exact (forall x1 x2, Aeq x1 x2 -> IHIn (f x1) (g x2)).
    destruct x.
      exact (forall x1 x2, Aeq x1 x2 -> IHIn (f x1) (g x2)).
      exact (forall x1 x2, Aeq x2 x1 -> IHIn (f x1) (g x2)).
    exact (forall x1 x2, Aeq x1 x2 -> IHIn (f x1) (g x2)).
    destruct x.
      exact (forall x1 x2, Aeq x1 x2 -> IHIn (f x1) (g x2)).
      exact (forall x1 x2, Aeq x2 x1 -> IHIn (f x1) (g x2)).
    exact (forall x, IHIn (f x) (g x)).
Defined. 

Definition make_compatibility_goal :=
  (fun In Out f => make_compatibility_goal_aux In Out f f).

Record Morphism_Theory In Out : Type :=
  { Function : function_type_of_morphism_signature In Out;
    Compat : make_compatibility_goal In Out Function }.


(** The [iff] relation class *)

Definition Iff_Relation_Class : Relation_Class.
  eapply (@SymmetricReflexive unit _ iff).
  exact iff_sym.
  exact iff_refl.
Defined.

(** The [impl] relation class *)

Definition impl (A B: Prop) := A -> B.

Theorem impl_refl: reflexive _ impl.
Proof.
  hnf; unfold impl; tauto.
Qed.

Definition Impl_Relation_Class : Relation_Class.
  eapply (@AsymmetricReflexive unit tt _ impl).
  exact impl_refl.
Defined.

(** Every function is a morphism from Leibniz+ to Leibniz *)

Definition list_of_Leibniz_of_list_of_types: nelistT Type -> Arguments.
 induction 1.
   exact (singl (Leibniz _ a)).
   exact (necons (Leibniz _ a) IHX).
Defined.

Definition morphism_theory_of_function :
  forall (In: nelistT Type) (Out: Type),
    let In' := list_of_Leibniz_of_list_of_types In in
      let Out' := Leibniz _ Out in
	function_type_of_morphism_signature In' Out' ->
	Morphism_Theory In' Out'.
  intros.
  exists X.
  induction In;  unfold make_compatibility_goal; simpl.
    reflexivity.
    intro; apply (IHIn (X x)).
Defined.

(** Every predicate is a morphism from Leibniz+ to Iff_Relation_Class *)

Definition morphism_theory_of_predicate :
  forall (In: nelistT Type),
    let In' := list_of_Leibniz_of_list_of_types In in
      function_type_of_morphism_signature In' Iff_Relation_Class ->
      Morphism_Theory In' Iff_Relation_Class.
  intros.
  exists X.
  induction In;  unfold make_compatibility_goal; simpl.
    intro; apply iff_refl.
    intro; apply (IHIn (X x)).
Defined.

(** * Utility functions to prove that every transitive relation is a morphism *)

Definition equality_morphism_of_symmetric_areflexive_transitive_relation:
 forall (A: Type)(Aeq: relation A)(sym: symmetric _ Aeq)(trans: transitive _ Aeq),
  let ASetoidClass := SymmetricAreflexive _ sym in
   (Morphism_Theory (necons ASetoidClass (singl ASetoidClass)) Iff_Relation_Class).
 intros.
 exists Aeq.
 unfold make_compatibility_goal; simpl; split; eauto.
Defined.

Definition equality_morphism_of_symmetric_reflexive_transitive_relation:
 forall (A: Type)(Aeq: relation A)(refl: reflexive _ Aeq)(sym: symmetric _ Aeq)
  (trans: transitive _ Aeq), let ASetoidClass := SymmetricReflexive _ sym refl in
   (Morphism_Theory (necons ASetoidClass (singl ASetoidClass)) Iff_Relation_Class).
 intros.
 exists Aeq.
 unfold make_compatibility_goal; simpl; split; eauto.
Defined.

Definition equality_morphism_of_asymmetric_areflexive_transitive_relation:
 forall (A: Type)(Aeq: relation A)(trans: transitive _ Aeq),
  let ASetoidClass1 := AsymmetricAreflexive Contravariant Aeq in
  let ASetoidClass2 := AsymmetricAreflexive Covariant Aeq in
   (Morphism_Theory (necons ASetoidClass1 (singl ASetoidClass2)) Impl_Relation_Class).
 intros.
 exists Aeq.
 unfold make_compatibility_goal; simpl; unfold impl; eauto.
Defined.

Definition equality_morphism_of_asymmetric_reflexive_transitive_relation:
 forall (A: Type)(Aeq: relation A)(refl: reflexive _ Aeq)(trans: transitive _ Aeq),
  let ASetoidClass1 := AsymmetricReflexive Contravariant refl in
  let ASetoidClass2 := AsymmetricReflexive Covariant refl in
   (Morphism_Theory (necons ASetoidClass1 (singl ASetoidClass2)) Impl_Relation_Class).
 intros.
 exists Aeq.
 unfold make_compatibility_goal; simpl; unfold impl; eauto.
Defined.

(** * The CIC part of the reflexive tactic ([setoid_rewrite]) *)

Inductive rewrite_direction : Type :=
  | Left2Right
  | Right2Left.

Implicit Type dir: rewrite_direction.

Definition variance_of_argument_class : Argument_Class -> option variance.
  destruct 1.
  exact None.
  exact (Some v).
  exact None.
  exact (Some v).
  exact None.
Defined.

Definition opposite_direction :=
  fun dir =>
    match dir with
      | Left2Right => Right2Left
      | Right2Left => Left2Right
   end.

Lemma opposite_direction_idempotent:
  forall dir, (opposite_direction (opposite_direction dir)) = dir.
Proof.
  destruct dir; reflexivity.
Qed.

Inductive check_if_variance_is_respected :
  option variance -> rewrite_direction -> rewrite_direction ->  Prop :=
  | MSNone : forall dir dir', check_if_variance_is_respected None dir dir'
  | MSCovariant : forall dir, check_if_variance_is_respected (Some Covariant) dir dir
  | MSContravariant :
    forall dir,
      check_if_variance_is_respected (Some Contravariant) dir (opposite_direction dir).

Definition relation_class_of_reflexive_relation_class:
  Reflexive_Relation_Class -> Relation_Class.
  induction 1.
  exact (SymmetricReflexive _ s r).
  exact (AsymmetricReflexive tt r).
  exact (Leibniz _ T).
Defined.

Definition relation_class_of_areflexive_relation_class:
  Areflexive_Relation_Class -> Relation_Class.
  induction 1.
    exact (SymmetricAreflexive _ s).
    exact (AsymmetricAreflexive tt Aeq).
Defined.

Definition carrier_of_reflexive_relation_class :=
  fun R => carrier_of_relation_class (relation_class_of_reflexive_relation_class R).

Definition carrier_of_areflexive_relation_class :=
  fun R => carrier_of_relation_class (relation_class_of_areflexive_relation_class R).

Definition relation_of_areflexive_relation_class :=
  fun R => relation_of_relation_class (relation_class_of_areflexive_relation_class R).

Inductive Morphism_Context Hole dir : Relation_Class -> rewrite_direction ->  Type :=
  | App :
    forall In Out dir',
      Morphism_Theory In Out -> Morphism_Context_List Hole dir dir' In ->
      Morphism_Context Hole dir Out dir'
  | ToReplace : Morphism_Context Hole dir Hole dir
  | ToKeep :
    forall S dir',
      carrier_of_reflexive_relation_class S ->
      Morphism_Context Hole dir (relation_class_of_reflexive_relation_class S) dir'
  | ProperElementToKeep :
    forall S dir' (x: carrier_of_areflexive_relation_class S),
      relation_of_areflexive_relation_class S x x ->
      Morphism_Context Hole dir (relation_class_of_areflexive_relation_class S) dir'
with Morphism_Context_List Hole dir :
   rewrite_direction -> Arguments -> Type
:=
    fcl_singl :
      forall S dir' dir'',
       check_if_variance_is_respected (variance_of_argument_class S) dir' dir'' ->
        Morphism_Context Hole dir (relation_class_of_argument_class S) dir' ->
         Morphism_Context_List Hole dir dir'' (singl S)
 | fcl_cons :
      forall S L dir' dir'',
       check_if_variance_is_respected (variance_of_argument_class S) dir' dir'' ->
        Morphism_Context Hole dir (relation_class_of_argument_class S) dir' ->
         Morphism_Context_List Hole dir dir'' L ->
          Morphism_Context_List Hole dir dir'' (necons S L).

Scheme Morphism_Context_rect2 := Induction for Morphism_Context  Sort Type
with Morphism_Context_List_rect2 := Induction for Morphism_Context_List Sort Type.

Definition product_of_arguments : Arguments -> Type.
  induction 1.
  exact (carrier_of_relation_class a).
  exact (prod (carrier_of_relation_class a) IHX).
Defined.

Definition get_rewrite_direction: rewrite_direction -> Argument_Class -> rewrite_direction.
  intros dir R.
  destruct (variance_of_argument_class R).
  destruct v.
    exact dir.                      (* covariant *)
    exact (opposite_direction dir). (* contravariant *)
   exact dir.                       (* symmetric relation *)
Defined.

Definition directed_relation_of_relation_class:
  forall dir (R: Relation_Class),
    carrier_of_relation_class R -> carrier_of_relation_class R -> Prop.
  destruct 1.
    exact (@relation_of_relation_class unit).
    intros; exact (relation_of_relation_class _ X0 X).
Defined.

Definition directed_relation_of_argument_class:
  forall dir (R: Argument_Class),
    carrier_of_relation_class R -> carrier_of_relation_class R -> Prop.
  intros dir R.
  rewrite <-
    (about_carrier_of_relation_class_and_relation_class_of_argument_class R).
  exact (directed_relation_of_relation_class dir (relation_class_of_argument_class R)).
Defined.


Definition relation_of_product_of_arguments:
  forall dir In,
    product_of_arguments In -> product_of_arguments In -> Prop.
  induction In.
    simpl.
      exact (directed_relation_of_argument_class (get_rewrite_direction dir a) a).

    simpl; intros.
      destruct X; destruct X0.
   apply and.
     exact
      (directed_relation_of_argument_class (get_rewrite_direction dir a) a c c0).
     exact (IHIn p p0).
Defined. 

Definition apply_morphism:
  forall In Out (m: function_type_of_morphism_signature In Out)
    (args: product_of_arguments In), carrier_of_relation_class Out.
  intros.
  induction In.
    exact (m args).
    simpl in m, args.
    destruct args.
    exact (IHIn (m c) p).
Defined.

Theorem apply_morphism_compatibility_Right2Left:
  forall In Out (m1 m2: function_type_of_morphism_signature In Out)
    (args1 args2: product_of_arguments In),
    make_compatibility_goal_aux _ _ m1 m2 ->
    relation_of_product_of_arguments Right2Left _ args1 args2 ->
    directed_relation_of_relation_class Right2Left _
    (apply_morphism _ _ m2 args1)
    (apply_morphism _ _ m1 args2).
  induction In; intros.
    simpl in m1, m2, args1, args2, H0 |- *.
    destruct a; simpl in H; hnf in H0.
      apply H; exact H0.
      destruct v; simpl in H0; apply H; exact H0.
      apply H; exact H0.
      destruct v; simpl in H0; apply H; exact H0.
      rewrite H0; apply H; exact H0.

   simpl in m1, m2, args1, args2, H0 |- *.
   destruct args1; destruct args2; simpl.
   destruct H0.
   simpl in H.
   destruct a; simpl in H.
     apply IHIn.
       apply H; exact H0.
       exact H1.
     destruct v.
       apply IHIn.
         apply H; exact H0.
         exact H1.
       apply IHIn.
         apply H; exact H0.       
          exact H1.
     apply IHIn.
       apply H; exact H0.
       exact H1.
     destruct v.
       apply IHIn.
         apply H; exact H0.
         exact H1.
       apply IHIn.
         apply H; exact H0.       
          exact H1.
    rewrite H0; apply IHIn.
      apply H.
      exact H1.
Qed.

Theorem apply_morphism_compatibility_Left2Right:
  forall In Out (m1 m2: function_type_of_morphism_signature In Out)
    (args1 args2: product_of_arguments In),
    make_compatibility_goal_aux _ _ m1 m2 ->
    relation_of_product_of_arguments Left2Right _ args1 args2 ->
    directed_relation_of_relation_class Left2Right _
    (apply_morphism _ _ m1 args1)
    (apply_morphism _ _ m2 args2).
Proof.
  induction In; intros.
    simpl in m1, m2, args1, args2, H0 |- *.
    destruct a; simpl in H; hnf in H0.
      apply H; exact H0.
      destruct v; simpl in H0; apply H; exact H0.
      apply H; exact H0.
      destruct v; simpl in H0; apply H; exact H0.
      rewrite H0; apply H; exact H0.

  simpl in m1, m2, args1, args2, H0 |- *.
    destruct args1; destruct args2; simpl.
    destruct H0.
    simpl in H.
    destruct a; simpl in H.
      apply IHIn.
        apply H; exact H0.
        exact H1.
      destruct v.
        apply IHIn.
          apply H; exact H0.
          exact H1.
        apply IHIn.
          apply H; exact H0.       
           exact H1.
        apply IHIn.
          apply H; exact H0.
          exact H1.
        apply IHIn.
          destruct v; simpl in H, H0; apply H; exact H0. 
            exact H1.
      rewrite H0; apply IHIn.
        apply H.
        exact H1.
Qed.

Definition interp :
 forall Hole dir Out dir', carrier_of_relation_class Hole ->
  Morphism_Context Hole dir Out dir' -> carrier_of_relation_class Out.
 intros Hole dir Out dir' H t.
 elim t using
  (@Morphism_Context_rect2 Hole dir (fun S _ _ => carrier_of_relation_class S)
    (fun _ L fcl => product_of_arguments L));
  intros.
   exact (apply_morphism _ _ (Function m) X).
   exact H.
   exact c.
   exact x.
   simpl;
     rewrite <-
       (about_carrier_of_relation_class_and_relation_class_of_argument_class S);
     exact X.
   split.
     rewrite <-
       (about_carrier_of_relation_class_and_relation_class_of_argument_class S);
       exact X.
       exact X0.
Defined.

(* CSC: interp and interp_relation_class_list should be mutually defined, since
   the proof term of each one contains the proof term of the other one. However
   I cannot do that interactively (I should write the Fix by hand) *)
Definition interp_relation_class_list :
  forall Hole dir dir' (L: Arguments), carrier_of_relation_class Hole ->
    Morphism_Context_List Hole dir dir' L -> product_of_arguments L.
  intros Hole dir dir' L H t.
  elim t using
    (@Morphism_Context_List_rect2 Hole dir (fun S _ _ => carrier_of_relation_class S)
      (fun _ L fcl => product_of_arguments L));
    intros.
  exact (apply_morphism _ _ (Function m) X).
  exact H.
  exact c.
  exact x.
  simpl;
    rewrite <-
      (about_carrier_of_relation_class_and_relation_class_of_argument_class S);
      exact X.
  split.
  rewrite <-
    (about_carrier_of_relation_class_and_relation_class_of_argument_class S);
    exact X.
  exact X0.
Defined.

Theorem setoid_rewrite:
  forall Hole dir Out dir' (E1 E2: carrier_of_relation_class Hole)
    (E: Morphism_Context Hole dir Out dir'),
    (directed_relation_of_relation_class dir Hole E1 E2) ->
    (directed_relation_of_relation_class dir' Out (interp E1 E) (interp E2 E)).
Proof.
  intros.
  elim E using
    (@Morphism_Context_rect2 Hole dir
      (fun S dir'' E => directed_relation_of_relation_class dir'' S (interp E1 E) (interp E2 E))
      (fun dir'' L fcl =>
        relation_of_product_of_arguments dir'' _
        (interp_relation_class_list E1 fcl)
        (interp_relation_class_list E2 fcl))); intros.
  change (directed_relation_of_relation_class dir'0 Out0
    (apply_morphism _ _ (Function m) (interp_relation_class_list E1 m0))
    (apply_morphism _ _ (Function m) (interp_relation_class_list E2 m0))).
  destruct dir'0.
    apply apply_morphism_compatibility_Left2Right.
      exact (Compat m).
      exact H0.
    apply apply_morphism_compatibility_Right2Left.
      exact (Compat m).
      exact H0.

  exact H.

  unfold interp, Morphism_Context_rect2.
  (* CSC: reflexivity used here *)
  destruct S; destruct dir'0; simpl; (apply r || reflexivity).
  
  destruct dir'0; exact r.

  destruct S; unfold directed_relation_of_argument_class; simpl in H0 |- *;
    unfold get_rewrite_direction; simpl.
  destruct dir'0; destruct dir'';
    (exact H0 ||
      unfold directed_relation_of_argument_class; simpl; apply s; exact H0).
  (* the following mess with generalize/clear/intros is to help Coq resolving *)
  (* second order unification problems.                                       *)
  generalize m c H0; clear H0 m c; inversion c;
    generalize m c; clear m c; rewrite <- H1; rewrite <- H2; intros;
      (exact H3 || rewrite (opposite_direction_idempotent dir'0); apply H3).
  destruct dir'0; destruct dir'';
    (exact H0 ||
      unfold directed_relation_of_argument_class; simpl; apply s; exact H0).
  (* the following mess with generalize/clear/intros is to help Coq resolving *)
  (* second order unification problems.                                       *)
  generalize m c H0; clear H0 m c; inversion c;
    generalize m c; clear m c; rewrite <- H1; rewrite <- H2; intros;
      (exact H3 || rewrite (opposite_direction_idempotent dir'0); apply H3).
  destruct dir'0; destruct dir''; (exact H0 || hnf; symmetry; exact H0).

  change
    (directed_relation_of_argument_class (get_rewrite_direction dir'' S) S
       (eq_rect _ (fun T : Type => T) (interp E1 m) _
         (about_carrier_of_relation_class_and_relation_class_of_argument_class S))
       (eq_rect _ (fun T : Type => T) (interp E2 m) _
         (about_carrier_of_relation_class_and_relation_class_of_argument_class S)) /\
       relation_of_product_of_arguments dir'' _
       (interp_relation_class_list E1 m0) (interp_relation_class_list E2 m0)).
  split.
  clear m0 H1; destruct S; simpl in H0 |- *; unfold get_rewrite_direction; simpl.
    destruct dir''; destruct dir'0; (exact H0 || hnf; apply s; exact H0).
      inversion c.
        rewrite <- H3; exact H0.
        rewrite (opposite_direction_idempotent dir'0); exact H0.
      destruct dir''; destruct dir'0; (exact H0 || hnf; apply s; exact H0).
      inversion c.
        rewrite <- H3; exact H0.
        rewrite (opposite_direction_idempotent dir'0); exact H0.
      destruct dir''; destruct dir'0; (exact H0 || hnf; symmetry; exact H0).
    exact H1.
  Qed.
