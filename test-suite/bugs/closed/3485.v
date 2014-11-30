Set Universe Polymorphism.
Set Primitive Projections.
Reserved Infix "o" (at level 40, left associativity).
Definition relation (A : Type) := A -> A -> Type.
Class Transitive {A} (R : relation A) := transitivity : forall x y z, R x y -> R y z -> R x z.
Tactic Notation "etransitivity" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  refine (@transitivity _ R _ x y z _ _).
Tactic Notation "etransitivity" := etransitivity _.
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.
Notation "x .1" := (projT1 x) (at level 3) : fibration_scope.
Notation "x .2" := (projT2 x) (at level 3) : fibration_scope.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z := match p, q with idpath, idpath => idpath end.
Instance transitive_paths {A} : Transitive (@paths A) | 0 := @concat A.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y := match p with idpath => u end.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.
Class Contr_internal (A : Type) := { center : A ; contr : (forall y : A, center = y) }.
Generalizable Variables X A B C f g n.
Definition projT1_path `{P : A -> Type} {u v : sigT P} (p : u = v) : u.1 = v.1 := ap (@projT1 _ _) p.
Notation "p ..1" := (projT1_path p) (at level 3) : fibration_scope.
Ltac simpl_do_clear tac term :=
  let H := fresh in
  assert (H := term);
    simpl in H |- *;
    tac H;
    clear H.
Set Implicit Arguments.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Record PreCategory :=
  { object :> Type;
    morphism : object -> object -> Type;

    identity : forall x, morphism x x;
    compose : forall s d d',
                morphism d d'
                -> morphism s d
                -> morphism s d'
                            where "f 'o' g" := (compose f g);

    left_identity : forall a b (f : morphism a b), identity b o f = f;
    right_identity : forall a b (f : morphism a b), f o identity a = f }.
Arguments identity {C%category} / x%object : rename.
Arguments compose {C%category} / {s d d'}%object (m1 m2)%morphism : rename.
Infix "o" := compose : morphism_scope.
Notation "1" := (identity _) : morphism_scope.
Delimit Scope functor_scope with functor.
Local Open Scope morphism_scope.
Record Functor (C D : PreCategory) :=
  { object_of :> C -> D;
    morphism_of : forall s d, morphism C s d
                              -> morphism D (object_of s) (object_of d);
    identity_of : forall x, morphism_of _ _ (identity x)
                            = identity (object_of x) }.
Bind Scope functor_scope with Functor.
Arguments morphism_of [C%category] [D%category] F%functor / [s%object d%object] m%morphism : rename.
Notation "F '_1' m" := (morphism_of F m) (at level 10, no associativity) : morphism_scope.
Section composition.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variable G : Functor D E.
  Variable F : Functor C D.

  Local Notation c_object_of c := (G (F c)) (only parsing).
  Local Notation c_morphism_of m := (morphism_of G (morphism_of F m)) (only parsing).

  Definition compose_identity_of x
  : c_morphism_of (identity x) = identity (c_object_of x)
    := transport (@paths _ _)
                 (identity_of G _)
                 (ap (@morphism_of _ _ G _ _) (identity_of F x)).

  Definition composeF : Functor C E
    := Build_Functor
         C E
         (fun c => G (F c))
         (fun _ _ m => morphism_of G (morphism_of F m))
         compose_identity_of.
End composition.
Infix "o" := composeF : functor_scope.

Definition identityF C : Functor C C
  := Build_Functor C C
                   (fun x => x)
                   (fun _ _ x => x)
                   (fun _ => idpath).
Notation "1" := (identityF _) : functor_scope.

Record NaturalTransformation C D (F G : Functor C D) := { components_of :> forall c, morphism D (F c) (G c) }.

Section unit.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.

  Definition AdjunctionUnit :=
    { T : NaturalTransformation 1 (G o F)
                                & forall (c : C) (d : D) (f : morphism C c (G d)),
                                    Contr_internal { g : morphism D (F c) d & G _1 g o T c = f }
    }.
End unit.
Variable C : PreCategory.
Variable D : PreCategory.
Variable F : Functor C D.
Variable G : Functor D C.

Definition zig__of__adjunction_unit
           (A : AdjunctionUnit F G)
           (Y : C)
           (eta := A.1)
           (eps := fun X => (@center _ (A.2 (G X) X 1)).1)
: G _1 (eps (F Y) o F _1 (eta Y)) o eta Y = eta Y
  -> eps (F Y) o F _1 (eta Y) = 1.
Proof.
  intros.
  etransitivity; [ symmetry | ];
  simpl_do_clear
    ltac:(fun H => apply H)
           (fun y H => (@contr _ (A.2 _ _ (A.1 Y)) (y; H))..1);
  try assumption.
  simpl.
  rewrite ?@identity_of, ?@left_identity, ?@right_identity;
    reflexivity.
Qed.
