
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$: i*)

(*
Set Implicit Arguments.

(* DEFINITIONS OF Relation_Class AND n-ARY Morphism_Theory *)

Definition is_reflexive (A: Type) (Aeq: A -> A -> Prop) : Prop :=
 forall x:A, Aeq x x.

Definition is_symmetric (A: Type) (Aeq: A -> A -> Prop) : Prop :=
 forall (x y:A), Aeq x y -> Aeq y x.

Inductive Relation_Class : Type :=
   Reflexive : forall A Aeq, (@is_reflexive A Aeq) -> Relation_Class
 | Leibniz : Type -> Relation_Class.

Implicit Type Hole Out: Relation_Class.

Definition carrier_of_relation_class : Relation_Class -> Type.
 intro; case X; intros.
 exact A.
 exact T.
Defined.

Inductive nelistT (A : Type) : Type :=
   singl : A -> (nelistT A)
 | cons : A -> (nelistT A) -> (nelistT A).

Implicit Type In: (nelistT Relation_Class).

Definition function_type_of_morphism_signature :
 (nelistT Relation_Class) -> Relation_Class -> Type.
  intros In Out.
  induction In.
    exact (carrier_of_relation_class a -> carrier_of_relation_class Out).
    exact (carrier_of_relation_class a -> IHIn).
Defined. 

Definition make_compatibility_goal_aux:
 forall In Out
  (f g: function_type_of_morphism_signature In Out), Prop.
 intros; induction In; simpl in f, g.
   induction a; destruct Out; simpl in f, g.
     exact (forall (x1 x2: A), (Aeq x1 x2) -> (Aeq0 (f x1) (g x2))).
     exact (forall (x1 x2: A), (Aeq x1 x2) -> f x1 = g x2).
     exact (forall (x: T), (Aeq (f x) (g x))).
     exact (forall (x: T), f x = g x).
  induction a; simpl in f, g.
    exact (forall (x1 x2: A), (Aeq x1 x2) -> IHIn (f x1) (g x2)).
    exact (forall (x: T), IHIn (f x) (g x)).
Defined. 

Definition make_compatibility_goal :=
 (fun In Out f => make_compatibility_goal_aux In Out f f).

Record Morphism_Theory In Out : Type :=
   {Function : function_type_of_morphism_signature In Out;
    Compat : make_compatibility_goal In Out Function}.

Definition list_of_Leibniz_of_list_of_types:
 nelistT Type -> nelistT Relation_Class.
 induction 1.
   exact (singl (Leibniz a)).
   exact (cons (Leibniz a) IHX).
Defined.

(* every function is a morphism from Leibniz+ to Leibniz *)
Definition morphism_theory_of_function :
 forall (In: nelistT Type) (Out: Type),
  let In' := list_of_Leibniz_of_list_of_types In in
  let Out' := Leibniz Out in
   function_type_of_morphism_signature In' Out' ->
    Morphism_Theory In' Out'.
  intros.
  exists X.
  induction In;  unfold make_compatibility_goal; simpl.
    reflexivity.
    intro; apply (IHIn (X x)).
Defined.

(* THE Prop RELATION CLASS *)

Add Relation Prop iff reflexivity proved by iff_refl symmetry proved by iff_sym.

Definition Prop_Relation_Class : Relation_Class.
 eapply (@Reflexive _ iff).
 exact iff_refl.
Defined.

(* every predicate is  morphism from Leibniz+ to Prop_Relation_Class *)
Definition morphism_theory_of_predicate :
 forall (In: nelistT Type),
  let In' := list_of_Leibniz_of_list_of_types In in
   function_type_of_morphism_signature In' Prop_Relation_Class ->
    Morphism_Theory In' Prop_Relation_Class.
  intros.
  exists X.
  induction In;  unfold make_compatibility_goal; simpl.
    intro; apply iff_refl.
    intro; apply (IHIn (X x)).
Defined.

(* THE CIC PART OF THE REFLEXIVE TACTIC (SETOID REWRITE) *)

Inductive Morphism_Context Hole : Relation_Class -> Type :=
    App : forall In Out,
                Morphism_Theory In Out ->  Morphism_Context_List Hole In ->
                  Morphism_Context Hole Out
  | Toreplace : Morphism_Context Hole Hole
  | Tokeep :
     forall (S: Relation_Class),
      carrier_of_relation_class S -> Morphism_Context Hole S
  | Imp :
      Morphism_Context Hole Prop_Relation_Class ->
       Morphism_Context Hole Prop_Relation_Class ->
        Morphism_Context Hole Prop_Relation_Class
with Morphism_Context_List Hole: nelistT Relation_Class -> Type :=
    fcl_singl :
      forall (S: Relation_Class), Morphism_Context Hole S ->
       Morphism_Context_List Hole (singl S)
 | fcl_cons :
      forall (S: Relation_Class) (L: nelistT Relation_Class),
       Morphism_Context Hole S -> Morphism_Context_List Hole L ->
        Morphism_Context_List Hole (cons S L).

Scheme Morphism_Context_rect2 := Induction for Morphism_Context  Sort Type
with Morphism_Context_List_rect2 := Induction for Morphism_Context_List Sort Type.

Inductive prodT (A B: Type) : Type :=
 pairT : A -> B -> prodT A B.

Definition product_of_relation_class_list : nelistT Relation_Class -> Type.
 induction 1.
   exact (carrier_of_relation_class a).
   exact (prodT (carrier_of_relation_class a) IHX).
Defined.

Definition relation_of_relation_class:
 forall Out,
  carrier_of_relation_class Out -> carrier_of_relation_class Out -> Prop.
 destruct Out.
   exact Aeq.
   exact (@eq T).
Defined.

Definition relation_of_product_of_relation_class_list:
 forall In,
  product_of_relation_class_list In -> product_of_relation_class_list In -> Prop.
 induction In.
   exact (relation_of_relation_class a).

   simpl; intros.
   destruct X; destruct X0.
   exact (relation_of_relation_class a c c0 /\ IHIn p p0).
Defined. 

Definition apply_morphism:
 forall In Out (m: function_type_of_morphism_signature In Out)
  (args: product_of_relation_class_list In), carrier_of_relation_class Out.
 intros.
 induction In.
   exact (m args).
   simpl in m, args.
   destruct args.
   exact (IHIn (m c) p).
Defined.

Theorem apply_morphism_compatibility:
 forall In Out (m1 m2: function_type_of_morphism_signature In Out)
   (args1 args2: product_of_relation_class_list In),
     make_compatibility_goal_aux _ _ m1 m2 ->
      relation_of_product_of_relation_class_list _ args1 args2 ->
        relation_of_relation_class _
         (apply_morphism _ _ m1 args1)
         (apply_morphism _ _ m2 args2).
  intros.
  induction In.
    simpl; simpl in m1, m2, args1, args2, H0.
    destruct a; destruct Out.
      apply H; exact H0.
      simpl; apply H; exact H0.
      simpl; rewrite H0; apply H.
      simpl; rewrite H0; apply H.
   simpl in args1, args2, H0.
   destruct args1; destruct args2; simpl.
   destruct H0.
   simpl in H.
   destruct a; simpl in H.
     apply IHIn.
       apply H; exact H0.
       exact H1.
    rewrite H0; apply IHIn.
      apply H.
      exact H1.
Qed.

Definition interp :
 forall Hole Out, carrier_of_relation_class Hole ->
  Morphism_Context Hole Out -> carrier_of_relation_class Out.
 intros Hole Out H t.
 elim t using
  (@Morphism_Context_rect2 Hole (fun S _ => carrier_of_relation_class S)
    (fun L fcl => product_of_relation_class_list L));
  intros.
   exact (apply_morphism _ _ (Function m) X).
   exact H.
   exact c.
   exact (X -> X0).
   exact X.
   split; [ exact X | exact X0 ].
Defined.

(*CSC: interp and interp_relation_class_list should be mutually defined, since
   the proof term of each one contains the proof term of the other one. However
   I cannot do that interactively (I should write the Fix by hand) *)
Definition interp_relation_class_list :
 forall Hole (L: nelistT Relation_Class), carrier_of_relation_class Hole ->
  Morphism_Context_List Hole L -> product_of_relation_class_list L.
 intros Hole L H t.
 elim t using
  (@Morphism_Context_List_rect2 Hole (fun S _ => carrier_of_relation_class S)
    (fun L fcl => product_of_relation_class_list L));
 intros.
   exact (apply_morphism _ _ (Function m) X).
   exact H.
   exact c.
   exact (X -> X0).
   exact X.
   split; [ exact X | exact X0 ].
Defined.

Theorem setoid_rewrite:
 forall Hole Out (E1 E2: carrier_of_relation_class Hole)
  (E: Morphism_Context Hole Out),
   (relation_of_relation_class Hole E1 E2) ->
    (relation_of_relation_class Out (interp E1 E) (interp E2 E)).
 intros.
 elim E using
   (@Morphism_Context_rect2 Hole
     (fun S E => relation_of_relation_class S (interp E1 E) (interp E2 E))
     (fun L fcl =>
       relation_of_product_of_relation_class_list _
        (interp_relation_class_list E1 fcl)
        (interp_relation_class_list E2 fcl)));
 intros.
   change (relation_of_relation_class Out0
    (apply_morphism _ _ (Function m) (interp_relation_class_list E1 m0))
    (apply_morphism _ _ (Function m) (interp_relation_class_list E2 m0))).
   apply apply_morphism_compatibility.
     exact (Compat m).
     exact H0.

   exact H.

   unfold interp, Morphism_Context_rect2.
   (*CSC: reflexivity used here*)
   destruct S.
     apply i.
     simpl; reflexivity.

   change
     (relation_of_relation_class Prop_Relation_Class
       (interp E1 m -> interp E1 m0) (interp E2 m -> interp E2 m0)).
   simpl; simpl in H0, H1.
   tauto.

  exact H0.

  change
    (relation_of_relation_class _ (interp E1 m) (interp E2 m) /\
     relation_of_product_of_relation_class_list _
       (interp_relation_class_list E1 m0) (interp_relation_class_list E2 m0)).
   split.
     exact H0.
     exact H1.
Qed.

(* BEGIN OF UTILITY/BACKWARD COMPATIBILITY PART *)

Record Setoid_Theory  (A: Type) (Aeq: A -> A -> Prop) : Prop := 
  {Seq_refl : forall x:A, Aeq x x;
   Seq_sym : forall x y:A, Aeq x y -> Aeq y x;
   Seq_trans : forall x y z:A, Aeq x y -> Aeq y z -> Aeq x z}.

Definition relation_class_of_setoid_theory:
 forall (A: Type) (Aeq: A -> A -> Prop),
  Setoid_Theory Aeq -> Relation_Class.
 intros.
 apply (@Reflexive _ Aeq).
 exact (Seq_refl H).
Defined.

Definition equality_morphism_of_setoid_theory:
 forall (A: Type) (Aeq: A -> A -> Prop) (ST: Setoid_Theory Aeq),
   let ASetoidClass := relation_class_of_setoid_theory ST in 
    (Morphism_Theory (cons ASetoidClass (singl ASetoidClass))
      Prop_Relation_Class).
 intros.
 exists Aeq.
 pose (sym   := Seq_sym ST);  clearbody sym.
 pose (trans := Seq_trans ST); clearbody trans.
 (*CSC: symmetry and transitivity used here *)
 unfold make_compatibility_goal; simpl; split; eauto.
Defined.

(* END OF UTILITY/BACKWARD COMPATIBILITY PART *)

(* A FEW EXAMPLES *)

Add Morphism iff : Iff_Morphism.
 tauto.
Defined.

(* impl IS A MORPHISM *)

Definition impl (A B: Prop) := A -> B.

Add Morphism impl : Impl_Morphism.
unfold impl; tauto.
Defined.

(* and IS A MORPHISM *)

Add Morphism and : And_Morphism.
 tauto.
Defined.

(* or IS A MORPHISM *)

Add Morphism or : Or_Morphism.
 tauto.
Defined.

(* not IS A MORPHISM *)

Add Morphism not : Not_Morphism.
 tauto.
Defined.

(* FOR BACKWARD COMPATIBILITY *)
Implicit Arguments Setoid_Theory [].
Implicit Arguments Seq_refl [].
Implicit Arguments Seq_sym [].
Implicit Arguments Seq_trans [].
*)
