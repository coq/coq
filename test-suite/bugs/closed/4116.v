(* File reduced by coq-bug-finder from original input, then from 13191 lines to 1315 lines, then from 1601 lines to 595 lines, then from 585 lines to 379 lines *)
(* coqc version 8.5beta1 (March 2015) compiled on Mar 3 2015 3:50:31 with OCaml 4.01.0
   coqtop version cagnode15:/afs/csail.mit.edu/u/j/jgross/coq-8.5,v8.5 (ac62cda8a4f488b94033b108c37556877232137a) *)

Axiom admit : False.
Ltac admit := exfalso; exact admit.

Global Set Primitive Projections.

Notation projT1 := proj1_sig (only parsing).
Notation projT2 := proj2_sig (only parsing).

Definition relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : relation A) :=
  reflexivity : forall x : A, R x x.

Class Symmetric {A} (R : relation A) :=
  symmetry : forall x y, R x y -> R y x.

Notation idmap := (fun x => x).
Delimit Scope function_scope with function.
Delimit Scope path_scope with path.
Delimit Scope fibration_scope with fibration.
Open Scope path_scope.
Open Scope fibration_scope.
Open Scope function_scope.

Notation pr1 := projT1.
Notation pr2 := projT2.

Notation "x .1" := (pr1 x) (at level 3, format "x '.1'") : fibration_scope.
Notation "x .2" := (pr2 x) (at level 3, format "x '.2'") : fibration_scope.

Notation compose := (fun g f x => g (f x)).

Notation "g 'o' f" := (compose g%function f%function) (at level 40, left associativity) : function_scope.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

Global Instance symmetric_paths {A} : Symmetric (@paths A) | 0 := @inverse A.

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.

Notation "1" := idpath : path_scope.

Notation "p @ q" := (concat p%path q%path) (at level 20) : path_scope.

Notation "p ^" := (inverse p%path) (at level 3, format "p '^'") : path_scope.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  match p with idpath => u end.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

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

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'") : function_scope.

Class Contr_internal (A : Type) := BuildContr {
                                       center : A ;
                                       contr : (forall y : A, center = y)
                                     }.

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Notation "n .+1" := (trunc_S n) (at level 2, left associativity, format "n .+1") : trunc_scope.
Local Open Scope trunc_scope.
Notation "-2" := minus_two (at level 0) : trunc_scope.
Notation "-1" := (-2.+1) (at level 0) : trunc_scope.
Notation "0" := (-1.+1) : trunc_scope.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | -2 => Contr_internal A
    | n'.+1 => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" :=
  unshelve refine (let __transparent_assert_hypothesis := (_ : type) in _);
  [
      | (
        let H := match goal with H := _ |- _ => constr:(H) end in
        rename H into name) ].

Definition transport_idmap_ap A (P : A -> Type) x y (p : x = y) (u : P x)
: transport P p u = transport idmap (ap P p) u
  := match p with idpath => idpath end.

Section Adjointify.

  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (isretr : Sect g f) (issect : Sect f g).

  Let issect' := fun x =>
                   ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

  Let is_adjoint' (a : A) : isretr (f a) = ap f (issect' a).
    admit.
  Defined.

  Definition isequiv_adjointify : IsEquiv f
    := BuildIsEquiv A B f g isretr issect' is_adjoint'.

End Adjointify.

Record TruncType (n : trunc_index) := BuildTruncType {
                                          trunctype_type : Type ;
                                          istrunc_trunctype_type : IsTrunc n trunctype_type
                                        }.
Arguments trunctype_type {_} _.

Coercion trunctype_type : TruncType >-> Sortclass.

Notation "n -Type" := (TruncType n) (at level 1) : type_scope.
Notation hSet := 0-Type.

Module Export Category.
  Module Export Core.
    Set Implicit Arguments.

    Delimit Scope morphism_scope with morphism.
    Delimit Scope category_scope with category.
    Delimit Scope object_scope with object.

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

          identity_identity : forall x, identity x o identity x = identity x
        }.
    Arguments identity {!C%category} / x%object : rename.
    Arguments compose {!C%category} / {s d d'}%object (m1 m2)%morphism : rename.

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

    Module Export CategoryCoreNotations.
      Infix "o" := compose : morphism_scope.
      Notation "1" := (identity _) : morphism_scope.
    End CategoryCoreNotations.

  End Core.

End Category.
Module Export Core.
  Set Implicit Arguments.

  Delimit Scope functor_scope with functor.

  Local Open Scope morphism_scope.

  Section Functor.
    Variables C D : PreCategory.

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
  Arguments morphism_of [C%category] [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.

End Core.
Module Export Morphisms.
  Set Implicit Arguments.

  Local Open Scope category_scope.
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

  Coercion morphism_isomorphic : Isomorphic >-> morphism.

  Local Infix "<~=~>" := Isomorphic (at level 70, no associativity) : category_scope.

  Section iso_equiv_relation.
    Variable C : PreCategory.

    Global Instance isisomorphism_identity (x : C) : IsIsomorphism (identity x)
      := {| morphism_inverse := identity x;
            left_inverse := left_identity C x x (identity x);
            right_inverse := right_identity C x x (identity x) |}.

    Global Instance isomorphic_refl : Reflexive (@Isomorphic C)
      := fun x : C => {| morphism_isomorphic := identity x |}.

    Definition idtoiso (x y : C) (H : x = y) : Isomorphic x y
      := match H in (_ = y0) return (x <~=~> y0) with
           | 1%path => reflexivity x
         end.
  End iso_equiv_relation.

End Morphisms.

Notation IsCategory C := (forall s d : object C, IsEquiv (@idtoiso C s d)).

Notation isotoid C s d := (@equiv_inv _ _ (@idtoiso C s d) _).

Notation cat_of obj :=
  (@Build_PreCategory obj
                      (fun x y => x -> y)
                      (fun _ x => x)
                      (fun _ _ _ f g => f o g)%core
                      (fun _ _ _ _ _ _ _ => idpath)
                      (fun _ _ _ => idpath)
                      (fun _ _ _ => idpath)
  ).
Definition set_cat : PreCategory := cat_of hSet.
Set Implicit Arguments.

Local Open Scope morphism_scope.

Section Grothendieck.
  Variable C : PreCategory.
  Variable F : Functor C set_cat.

  Record Pair :=
    {
      c : C;
      x : F c
    }.

  Local Notation Gmorphism s d :=
    { f : morphism C s.(c) d.(c)
    | morphism_of F f s.(x) = d.(x) }.

  Definition identity_H s
    := apD10 (identity_of F s.(c)) s.(x).

  Definition Gidentity s : Gmorphism s s.
  Proof.
    exists 1.
    apply identity_H.
  Defined.

  Definition Gcategory : PreCategory.
  Proof.
    unshelve refine (@Build_PreCategory
              Pair
              (fun s d => Gmorphism s d)
              Gidentity
              _
              _
              _
              _); admit.
  Defined.
End Grothendieck.

Lemma isotoid_1 {C} `{IsCategory C} {x : C} {H : IsIsomorphism (identity x)}
: isotoid C x x {| morphism_isomorphic := (identity x) ; isisomorphism_isomorphic := H |}
  = idpath.
  admit.
Defined.
Generalizable All Variables.

Section Grothendieck2.
  Context `{IsCategory C}.
  Variable F : Functor C set_cat.

  Instance iscategory_grothendieck_toset : IsCategory (Gcategory F).
  Proof.
    intros s d.
    unshelve refine (isequiv_adjointify _ _ _ _).
    {
      intro m.
      transparent assert (H' : (s.(c) = d.(c))).
      {
        apply (idtoiso C (x := s.(c)) (y := d.(c)))^-1%function.
        exists (m : morphism _ _ _).1.
        admit.

      }
      {
        transitivity {| x := transport (fun x => F x) H' s.(x) |}.
        admit.

        {
          change d with {| c := d.(c) ; x := d.(x) |}; simpl.
          apply ap.
          subst H'.
          simpl.
          refine (transport_idmap_ap _ (fun x => F x : Type) _ _ _ _ @ _ @ (m : morphism _ _ _).2).
          change (fun x => F x : Type) with (trunctype_type o object_of F)%function.
          admit.
        }
      }
    }
    {
      admit.
    }

    {
      intro x.
      hnf in s, d.
      destruct x.
      simpl.
      erewrite @isotoid_1.
