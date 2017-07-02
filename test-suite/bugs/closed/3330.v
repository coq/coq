Unset Strict Universe Declaration.
Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 12106 lines to 1070 lines *)
Set Universe Polymorphism.
Definition setleq (A : Type@{i}) (B : Type@{j}) := A : Type@{j}.

Inductive foo : Type@{l} := bar : foo . 
Section MakeEq.
  Variables (a : foo@{i}) (b : foo@{j}).

  Let t := ltac:(let ty := type of b in exact ty).
  Definition make_eq (x:=b) := a : t.
End MakeEq.

Definition same (x : foo@{i}) (y : foo@{i}) := x.

Section foo.

  Variables x : foo@{i}.
  Variables y : foo@{j}.
  
  Let AleqB := let foo := make_eq x y in (Type * Type)%type.

  Definition baz := same x y.
End foo.

Definition baz' := Eval unfold baz in baz@{i j k l}.

Module Export HoTT_DOT_Overture.
Module Export HoTT.
Module Export Overture.

Definition relation (A : Type) := A -> A -> Type.
Class Symmetric {A} (R : relation A) :=
  symmetry : forall x y, R x y -> R y x.

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) :=
  fun x => g (f x).

Notation "g 'o' f" := (compose g f) (at level 40, left associativity) : function_scope.

Open Scope function_scope.

Set Printing Universes. Set Printing All.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Notation "x = y :> A" := (@paths A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.

Delimit Scope path_scope with path.

Local Open Scope path_scope.

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

Instance symmetric_paths {A} : Symmetric (@paths A) | 0 := @inverse A.

Notation "1" := idpath : path_scope.

Notation "p @ q" := (concat p q) (at level 20) : path_scope.

Notation "p ^" := (inverse p) (at level 3) : path_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) : Type
  := forall x:A, f x = g x.

Hint Unfold pointwise_paths : typeclass_instances.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g
  := fun x => match h with idpath => 1 end.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Delimit Scope equiv_scope with equiv.

Local Open Scope equiv_scope.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.

Class Contr_internal (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Fixpoint nat_to_trunc_index (n : nat) : trunc_index
  := match n with
       | 0 => trunc_S (trunc_S minus_two)
       | S n' => trunc_S (nat_to_trunc_index n')
     end.

Coercion nat_to_trunc_index : nat >-> trunc_index.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

Notation IsHSet := (IsTrunc 0).

Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g
  :=
  (@apD10 A P f g)^-1.

End Overture.

End HoTT.

End HoTT_DOT_Overture.

Module Export HoTT_DOT_categories_DOT_Category_DOT_Core.

Module Export HoTT.
Module Export categories.
Module Export Category.
Module Export Core.
Set Universe Polymorphism.

Set Implicit Arguments.
Delimit Scope morphism_scope with morphism.

Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Set Printing Universes.
Set Printing All.
Record PreCategory :=
  Build_PreCategory' {
      object :> Type;
      morphism : object -> object -> Type;

      identity : forall x, morphism x x;
      compose : forall s d d',
                  morphism d d'
                  -> morphism s d
                  -> morphism s d'
                              where "f 'o' g" := (compose f g);

      associativity : forall x1 x2 x3 x4
                             (m1 : morphism x1 x2)
                             (m2 : morphism x2 x3)
                             (m3 : morphism x3 x4),
                        (m3 o m2) o m1 = m3 o (m2 o m1);

      associativity_sym : forall x1 x2 x3 x4
                                 (m1 : morphism x1 x2)
                                 (m2 : morphism x2 x3)
                                 (m3 : morphism x3 x4),
                            m3 o (m2 o m1) = (m3 o m2) o m1;

      left_identity : forall a b (f : morphism a b), identity b o f = f;
      right_identity : forall a b (f : morphism a b), f o identity a = f;

      identity_identity : forall x, identity x o identity x = identity x;

      trunc_morphism : forall s d, IsHSet (morphism s d)
    }.

Bind Scope category_scope with PreCategory.

Arguments identity [!C%category] x%object : rename.
Arguments compose [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

Definition Build_PreCategory
           object morphism compose identity
           associativity left_identity right_identity
  := @Build_PreCategory'
       object
       morphism
       compose
       identity
       associativity
       (fun _ _ _ _ _ _ _ => symmetry _ _ (associativity _ _ _ _ _ _ _))
       left_identity
       right_identity
       (fun _ => left_identity _ _ _).

Existing Instance trunc_morphism.

Hint Resolve @left_identity @right_identity @associativity : category morphism.

Module Export CategoryCoreNotations.

  Infix "o" := compose : morphism_scope.
End CategoryCoreNotations.
End Core.

End Category.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Category_DOT_Core.

Module Export HoTT_DOT_types_DOT_Forall.

Module Export HoTT.
Module Export types.
Module Export Forall.
Generalizable Variables A B f g e n.

Section AssumeFunext.

Global Instance trunc_forall `{P : A -> Type} `{forall a, IsTrunc n (P a)}
  : IsTrunc n (forall a, P a) | 100.

admit.
Defined.
End AssumeFunext.

End Forall.

End types.

End HoTT.

End HoTT_DOT_types_DOT_Forall.

Module Export HoTT_DOT_types_DOT_Prod.

Module Export HoTT.
Module Export types.
Module Export Prod.
Local Open Scope path_scope.

Definition path_prod_uncurried {A B : Type} (z z' : A * B)
  (pq : (fst z = fst z') * (snd z = snd z'))
  : (z = z')
  := match pq with (p,q) =>
       match z, z' return
         (fst z = fst z') -> (snd z = snd z') -> (z = z') with
         | (a,b), (a',b') => fun p q =>
           match p, q with
             idpath, idpath => 1
           end
       end p q
     end.

Definition path_prod {A B : Type} (z z' : A * B) :
  (fst z = fst z') -> (snd z = snd z') -> (z = z')
  := fun p q => path_prod_uncurried z z' (p,q).

Definition path_prod' {A B : Type} {x x' : A} {y y' : B}
  : (x = x') -> (y = y') -> ((x,y) = (x',y'))
  := fun p q => path_prod (x,y) (x',y') p q.

End Prod.

End types.

End HoTT.

End HoTT_DOT_types_DOT_Prod.

Module Export HoTT_DOT_categories_DOT_Functor_DOT_Core.

Module Export HoTT.
Module Export categories.
Module Export Functor.
Module Export Core.
Set Universe Polymorphism.

Set Implicit Arguments.
Delimit Scope functor_scope with functor.

Local Open Scope morphism_scope.

Section Functor.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Record Functor :=
    {
      object_of :> C -> D;
      morphism_of : forall s d, morphism C s d
                                -> morphism D (object_of s) (object_of d);
      composition_of : forall s d d'
                              (m1 : morphism C s d) (m2: morphism C d d'),
                         morphism_of _ _ (m2 o m1)
                         = (morphism_of _ _ m2) o (morphism_of _ _ m1);
      identity_of : forall x, morphism_of _ _ (identity x)
                              = identity (object_of x)
    }.

End Functor.
Bind Scope functor_scope with Functor.

Arguments morphism_of [C%category] [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.
Module Export FunctorCoreNotations.

  Notation "F '_1' m" := (morphism_of F m) (at level 10, no associativity) : morphism_scope.
End FunctorCoreNotations.
End Core.

End Functor.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Functor_DOT_Core.

Module Export HoTT_DOT_categories_DOT_Category_DOT_Morphisms.

Module Export HoTT.
Module Export categories.
Module Export Category.
Module Export Morphisms.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Class IsIsomorphism {C : PreCategory} {s d} (m : morphism C s d) :=
  {
    morphism_inverse : morphism C d s;
    left_inverse : morphism_inverse o m = identity _;
    right_inverse : m o morphism_inverse = identity _
  }.

Class Isomorphic {C : PreCategory} s d :=
  {
    morphism_isomorphic :> morphism C s d;
    isisomorphism_isomorphic :> IsIsomorphism morphism_isomorphic
  }.

Module Export CategoryMorphismsNotations.

  Infix "<~=~>" := Isomorphic (at level 70, no associativity) : category_scope.

End CategoryMorphismsNotations.
End Morphisms.

End Category.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Category_DOT_Morphisms.

Module Export HoTT_DOT_categories_DOT_Category_DOT_Dual.

Module Export HoTT.
Module Export categories.
Module Export Category.
Module Export Dual.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section opposite.

  Definition opposite (C : PreCategory) : PreCategory
    := @Build_PreCategory'
         C
         (fun s d => morphism C d s)
         (identity (C := C))
         (fun _ _ _ m1 m2 => m2 o m1)
         (fun _ _ _ _ _ _ _ => @associativity_sym _ _ _ _ _ _ _ _)
         (fun _ _ _ _ _ _ _ => @associativity _ _ _ _ _ _ _ _)
         (fun _ _ => @right_identity _ _ _)
         (fun _ _ => @left_identity _ _ _)
         (@identity_identity C)
         _.
End opposite.

Module Export CategoryDualNotations.

  Notation "C ^op" := (opposite C) (at level 3) : category_scope.
End CategoryDualNotations.
End Dual.

End Category.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Category_DOT_Dual.

Module Export HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.

Module Export HoTT.
Module Export categories.
Module Export Functor.
Module Export Composition.
Module Export Core.
Set Universe Polymorphism.

Set Implicit Arguments.
Local Open Scope morphism_scope.

Section composition.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variable G : Functor D E.
  Variable F : Functor C D.

  Local Notation c_object_of c := (G (F c)) (only parsing).

  Local Notation c_morphism_of m := (morphism_of G (morphism_of F m)) (only parsing).

  Let compose_composition_of' s d d'
      (m1 : morphism C s d) (m2 : morphism C d d')
  : c_morphism_of (m2 o m1) = c_morphism_of m2 o c_morphism_of m1.
admit.
Defined.
  Definition compose_composition_of s d d' m1 m2
    := Eval cbv beta iota zeta delta
            [compose_composition_of'] in
        @compose_composition_of' s d d' m1 m2.
  Let compose_identity_of' x
  : c_morphism_of (identity x) = identity (c_object_of x).

admit.
Defined.
  Definition compose_identity_of x
    := Eval cbv beta iota zeta delta
            [compose_identity_of'] in
        @compose_identity_of' x.
  Definition compose : Functor C E
    := Build_Functor
         C E
         (fun c => G (F c))
         (fun _ _ m => morphism_of G (morphism_of F m))
         compose_composition_of
         compose_identity_of.

End composition.
Module Export FunctorCompositionCoreNotations.

  Infix "o" := compose : functor_scope.
End FunctorCompositionCoreNotations.
End Core.

End Composition.

End Functor.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Functor_DOT_Composition_DOT_Core.

Module Export HoTT_DOT_categories_DOT_Functor_DOT_Dual.

Module Export HoTT.
Module Export categories.
Module Export Functor.
Module Export Dual.
Set Universe Polymorphism.

Set Implicit Arguments.

Section opposite.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Definition opposite (F : Functor C D) : Functor C^op D^op
    := Build_Functor (C^op) (D^op)
                     (object_of F)
                     (fun s d => morphism_of F (s := d) (d := s))
                     (fun d' d s m1 m2 => composition_of F s d d' m2 m1)
                     (identity_of F).

End opposite.
Module Export FunctorDualNotations.

  Notation "F ^op" := (opposite F) : functor_scope.
End FunctorDualNotations.
End Dual.

End Functor.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Functor_DOT_Dual.

Module Export HoTT_DOT_categories_DOT_Functor_DOT_Identity.

Module Export HoTT.
Module Export categories.
Module Export Functor.
Module Export Identity.
Set Universe Polymorphism.

Section identity.

  Definition identity C : Functor C C
    := Build_Functor C C
                     (fun x => x)
                     (fun _ _ x => x)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End identity.
Module Export FunctorIdentityNotations.

  Notation "1" := (identity _) : functor_scope.
End FunctorIdentityNotations.
End Identity.

End Functor.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Functor_DOT_Identity.

Module Export HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.

Module Export HoTT.
Module Export categories.
Module Export NaturalTransformation.
Module Export Core.
Set Universe Polymorphism.

Set Implicit Arguments.
Local Open Scope morphism_scope.

Section NaturalTransformation.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.

  Record NaturalTransformation :=
    Build_NaturalTransformation' {
        components_of :> forall c, morphism D (F c) (G c);
        commutes : forall s d (m : morphism C s d),
                     components_of d o F _1 m = G _1 m o components_of s;

        commutes_sym : forall s d (m : C.(morphism) s d),
                         G _1 m o components_of s = components_of d o F _1 m
      }.

End NaturalTransformation.
End Core.

End NaturalTransformation.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Core.

Module Export HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Dual.

Module Export HoTT.
Module Export categories.
Module Export NaturalTransformation.
Module Export Dual.
Set Universe Polymorphism.

Section opposite.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition opposite
             (F G : Functor C D)
             (T : NaturalTransformation F G)
  : NaturalTransformation G^op F^op
    := Build_NaturalTransformation' (G^op) (F^op)
                                    (components_of T)
                                    (fun s d => commutes_sym T d s)
                                    (fun s d => commutes T d s).

End opposite.

End Dual.

End NaturalTransformation.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Dual.

Module Export HoTT_DOT_categories_DOT_Category_DOT_Strict.

Module Export HoTT.
Module Export categories.
Module Export Category.
Module Export Strict.

Export Category.Core.
Set Universe Polymorphism.

End Strict.

End Category.

End categories.

End HoTT.

End HoTT_DOT_categories_DOT_Category_DOT_Strict.

Module Export HoTT.
Module Export categories.
Module Export Category.
Module Export Prod.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section prod.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Definition prod : PreCategory.

    refine (@Build_PreCategory
              (C * D)%type
              (fun s d => (morphism C (fst s) (fst d)
                           * morphism D (snd s) (snd d))%type)
              (fun x => (identity (fst x), identity (snd x)))
              (fun s d d' m2 m1 => (fst m2 o fst m1, snd m2 o snd m1))
              _
              _
              _
              _); admit.
  Defined.
End prod.
Module Export CategoryProdNotations.

  Infix "*" := prod : category_scope.
End CategoryProdNotations.
End Prod.

End Category.

End categories.

End HoTT.

Module Functor.
Module Export Prod.
Set Universe Polymorphism.

Set Implicit Arguments.
Local Open Scope morphism_scope.

Section proj.

  Context {C : PreCategory}.
  Context {D : PreCategory}.
  Definition fst : Functor (C * D) C
    := Build_Functor (C * D) C
                     (@fst _ _)
                     (fun _ _ => @fst _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition snd : Functor (C * D) D
    := Build_Functor (C * D) D
                     (@snd _ _)
                     (fun _ _ => @snd _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

End proj.

Section prod.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable D' : PreCategory.
  Definition prod (F : Functor C D) (F' : Functor C D')
  : Functor C (D * D')
    := Build_Functor
         C (D * D')
         (fun c => (F c, F' c))
         (fun s d m => (F _1 m, F' _1 m))
         (fun _ _ _ _ _ => path_prod' (composition_of F _ _ _ _ _)
                                      (composition_of F' _ _ _ _ _))
         (fun _ => path_prod' (identity_of F _) (identity_of F' _)).

End prod.
Local Infix "*" := prod : functor_scope.

Section pair.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable C' : PreCategory.
  Variable D' : PreCategory.
  Variable F : Functor C D.
  Variable F' : Functor C' D'.
  Definition pair : Functor (C * C') (D * D')
    := (F o fst) * (F' o snd).

End pair.

Module Export FunctorProdNotations.

  Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : functor_scope.
End FunctorProdNotations.
End Prod.

End Functor.

Module Export HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.

Module Export HoTT.
Module categories.
Module Export NaturalTransformation.
Module Export Composition.
Module Export Core.
Set Universe Polymorphism.

Set Implicit Arguments.
Local Open Scope path_scope.

Local Open Scope morphism_scope.

Section composition.

  Section compose.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variables F F' F'' : Functor C D.
    Variable T' : NaturalTransformation F' F''.

    Variable T : NaturalTransformation F F'.
    Local Notation CO c := (T' c o T c).

    Definition compose_commutes s d (m : morphism C s d)
    : CO d o morphism_of F m = morphism_of F'' m o CO s
      := (associativity _ _ _ _ _ _ _ _)
           @ ap (fun x => _ o x) (commutes T _ _ m)
           @ (associativity_sym _ _ _ _ _ _ _ _)
           @ ap (fun x => x o _) (commutes T' _ _ m)
           @ (associativity _ _ _ _ _ _ _ _).

    Definition compose_commutes_sym s d (m : morphism C s d)
    : morphism_of F'' m o CO s = CO d o morphism_of F m
      := (associativity_sym _ _ _ _ _ _ _ _)
           @ ap (fun x => x o _) (commutes_sym T' _ _ m)
           @ (associativity _ _ _ _ _ _ _ _)
           @ ap (fun x => _ o x) (commutes_sym T _ _ m)
           @ (associativity_sym _ _ _ _ _ _ _ _).

    Definition compose
    : NaturalTransformation F F''
      := Build_NaturalTransformation' F F''
                                      (fun c => CO c)
                                      compose_commutes
                                      compose_commutes_sym.

  End compose.
  End composition.
Module Export NaturalTransformationCompositionCoreNotations.

  Infix "o" := compose : natural_transformation_scope.
End NaturalTransformationCompositionCoreNotations.
End Core.

End Composition.

End NaturalTransformation.

End categories.

Set Universe Polymorphism.

Section path_natural_transformation.

  Context `{Funext}.
  Variable C : PreCategory.

  Variable D : PreCategory.
  Variables F G : Functor C D.

  Global Instance trunc_natural_transformation
  : IsHSet (NaturalTransformation F G).

admit.
Defined.
  Section path.

    Variables T U : NaturalTransformation F G.

    Lemma path'_natural_transformation
    : components_of T = components_of U
      -> T = U.

admit.
Defined.
    Lemma path_natural_transformation
    : components_of T == components_of U
      -> T = U.

    Proof.
      intros.
      apply path'_natural_transformation.
      apply path_forall; assumption.
    Qed.
  End path.
End path_natural_transformation.

Ltac path_natural_transformation :=
  repeat match goal with
           | _ => intro
           | _ => apply path_natural_transformation; simpl
         end.

Module Export Identity.
Set Universe Polymorphism.

Set Implicit Arguments.
Local Open Scope morphism_scope.

Local Open Scope path_scope.
Section identity.

  Variable C : PreCategory.
  Variable D : PreCategory.

  Section generalized.

    Variables F G : Functor C D.
    Hypothesis HO : object_of F = object_of G.
    Hypothesis HM : transport (fun GO => forall s d,
                                           morphism C s d
                                           -> morphism D (GO s) (GO d))
                              HO
                              (morphism_of F)
                    = morphism_of G.
    Local Notation CO c := (transport (fun GO => morphism D (F c) (GO c))
                                      HO
                                      (identity (F c))).

    Definition generalized_identity_commutes s d (m : morphism C s d)
    : CO d o morphism_of F m = morphism_of G m o CO s.

    Proof.
      case HM.
case HO.
      exact (left_identity _ _ _ _ @ (right_identity _ _ _ _)^).
    Defined.
    Definition generalized_identity_commutes_sym s d (m : morphism C s d)
    : morphism_of G m o CO s = CO d o morphism_of F m.

admit.
Defined.
    Definition generalized_identity
    : NaturalTransformation F G
      := Build_NaturalTransformation'
           F G
           (fun c => CO c)
           generalized_identity_commutes
           generalized_identity_commutes_sym.

  End generalized.
  Definition identity (F : Functor C D)
  : NaturalTransformation F F
    := Eval simpl in @generalized_identity F F 1 1.

End identity.
Module Export NaturalTransformationIdentityNotations.

  Notation "1" := (identity _) : natural_transformation_scope.
End NaturalTransformationIdentityNotations.
End Identity.

Module Export Laws.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.
Set Universe Polymorphism.

Local Open Scope natural_transformation_scope.
Section natural_transformation_identity.

  Context `{fs : Funext}.
  Variable C : PreCategory.

  Variable D : PreCategory.

  Lemma left_identity (F F' : Functor C D)
        (T : NaturalTransformation F F')
  : 1 o T = T.

  Proof.
    path_natural_transformation; auto with morphism.
  Qed.

  Lemma right_identity (F F' : Functor C D)
        (T : NaturalTransformation F F')
  : T o 1 = T.

  Proof.
    path_natural_transformation; auto with morphism.
  Qed.
End natural_transformation_identity.
Section associativity.

  Section nt.

    Context `{fs : Funext}.
    Definition associativity
               C D F G H I
               (V : @NaturalTransformation C D F G)
               (U : @NaturalTransformation C D G H)
               (T : @NaturalTransformation C D H I)
    : (T o U) o V = T o (U o V).

    Proof.
      path_natural_transformation.
      apply associativity.
    Qed.
  End nt.
End associativity.
End Laws.

Module Export FunctorCategory.
Module Export Core.
Import HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.HoTT.categories.
Set Universe Polymorphism.

Section functor_category.

  Context `{Funext}.
  Variable C : PreCategory.

  Variable D : PreCategory.

  Definition functor_category : PreCategory
    := @Build_PreCategory (Functor C D)
                          (@NaturalTransformation C D)
                          (@identity C D)
                          (@compose C D)
                          (@associativity _ C D)
                          (@left_identity _ C D)
                          (@right_identity _ C D)
                          _.

End functor_category.
Module Export FunctorCategoryCoreNotations.

  Notation "C -> D" := (functor_category C D) : category_scope.
End FunctorCategoryCoreNotations.
End Core.

End FunctorCategory.

Module Export Morphisms.
Set Universe Polymorphism.

Set Implicit Arguments.

Definition NaturalIsomorphism `{Funext} (C D : PreCategory) F G :=
  @Isomorphic (C -> D) F G.

Module Export FunctorCategoryMorphismsNotations.

  Infix "<~=~>" := NaturalIsomorphism : natural_transformation_scope.
End FunctorCategoryMorphismsNotations.
End Morphisms.

Module Export HSet.
Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.

Global Existing Instance iss.
End HSet.

Module Export Core.
Set Universe Polymorphism.

Notation cat_of obj :=
  (@Build_PreCategory obj
                      (fun x y => x -> y)
                      (fun _ x => x)
                      (fun _ _ _ f g => f o g)%core
                      (fun _ _ _ _ _ _ _ => idpath)
                      (fun _ _ _ => idpath)
                      (fun _ _ _ => idpath)
                      _).

Definition set_cat `{Funext} : PreCategory := cat_of hSet.
Set Universe Polymorphism.

Local Open Scope morphism_scope.

Section hom_functor.

  Context `{Funext}.
  Variable C : PreCategory.
  Local Notation obj_of c'c :=
    (BuildhSet
       (morphism
          C
          (fst (c'c : object (C^op * C)))
          (snd (c'c : object (C^op * C))))
       _).

  Let hom_functor_morphism_of s's d'd (hf : morphism (C^op * C) s's d'd)
  : morphism set_cat (obj_of s's) (obj_of d'd)
    := fun g => snd hf o g o fst hf.

  Definition hom_functor : Functor (C^op * C) set_cat.

    refine (Build_Functor (C^op * C) set_cat
                          (fun c'c => obj_of c'c)
                          hom_functor_morphism_of
                          _
                          _);
    subst hom_functor_morphism_of;
    simpl; admit.
  Defined.
End hom_functor.
Set Universe Polymorphism.

Import Category.Dual Functor.Dual.
Import Category.Prod Functor.Prod.
Import Functor.Composition.Core.
Import Functor.Identity.
Set Universe Polymorphism.

Local Open Scope functor_scope.
Local Open Scope natural_transformation_scope.
Section Adjunction.

  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.

 Let Adjunction_Type := 
    Eval simpl in (hom_functor D) o (F^op, 1) <~=~> (hom_functor C) o (1, G).

  Record AdjunctionHom :=
    {
      mate_of : 
        @NaturalIsomorphism H
                         (Prod.prod (Category.Dual.opposite C) D)
                         (@set_cat H)
                         (@compose (Prod.prod (Category.Dual.opposite C) D)
                            (Prod.prod (Category.Dual.opposite D) D)
                            (@set_cat H) (@hom_functor H D)
                            (@pair (Category.Dual.opposite C)
                               (Category.Dual.opposite D) D D
                               (@opposite C D F) (identity D)))
                         (@compose (Prod.prod (Category.Dual.opposite C) D)
                            (Prod.prod (Category.Dual.opposite C) C)
                            (@set_cat H) (@hom_functor H C)
                            (@pair (Category.Dual.opposite C)
                               (Category.Dual.opposite C) D C
                               (identity (Category.Dual.opposite C)) G))
    }.
End Adjunction.
(* Error: Illegal application:
The term "NaturalIsomorphism" of type
 "forall (H : Funext) (C D : PreCategory),
  (C -> D)%category -> (C -> D)%category -> Type"
cannot be applied to the terms
 "H" : "Funext"
 "(C ^op * D)%category" : "PreCategory"
 "set_cat" : "PreCategory"
 "hom_functor D o (F ^op, 1)" : "Functor (C ^op * D) set_cat"
 "hom_functor C o (1, G)" : "Functor (C ^op * D) set_cat"
The 5th term has type "Functor (C ^op * D) set_cat"
which should be coercible to "object (C ^op * D -> set_cat)".
*)
End Core.

End HoTT.

End HoTT_DOT_categories_DOT_NaturalTransformation_DOT_Composition_DOT_Core.
