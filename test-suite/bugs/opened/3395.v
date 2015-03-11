Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from originally 10918 lines, then 3649 lines to 3177 lines, then from 3189 lines to 3164 lines, then from 2653 lines to 2496 lines,  2653 lines, then from 1642 lines to 651 lines, then from 736 lines to 473 lines, then from 433 lines to 275 lines, then from 258 lines to 235 lines. *)
Generalizable All Variables.
Set Implicit Arguments.

Arguments fst {_ _} _.
Arguments snd {_ _} _.

Axiom cheat : forall {T}, T.

Reserved Notation "g 'o' f" (at level 40, left associativity).

Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y" := (paths x y) : type_scope.

Definition symmetry {A : Type} {x y : A} (p : x = y) : y = x
  := match p with idpath => idpath end.

Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Record PreCategory (object : Type) :=
  Build_PreCategory' {
      object :> Type := object;
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
Bind Scope category_scope with PreCategory.
Arguments PreCategory {_}.
Arguments identity {_} [!C%category] x%object : rename.

Arguments compose {_} [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

Infix "o" := compose : morphism_scope.

Delimit Scope functor_scope with functor.
Local Open Scope morphism_scope.
Record Functor `(C : @PreCategory objC, D : @PreCategory objD) :=
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
Bind Scope functor_scope with Functor.

Arguments morphism_of {_} [C%category] {_} [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.

Notation "F '_1' m" := (morphism_of F m) (at level 10, no associativity) : morphism_scope.

Class IsIsomorphism `{C : @PreCategory objC} {s d} (m : morphism C s d) :=
  {
    morphism_inverse : morphism C d s;
    left_inverse : morphism_inverse o m = identity _;
    right_inverse : m o morphism_inverse = identity _
  }.

Definition opposite `(C : @PreCategory objC) : PreCategory
  := @Build_PreCategory'
       C
       (fun s d => morphism C d s)
       (identity (C := C))
       (fun _ _ _ m1 m2 => m2 o m1)
       (fun _ _ _ _ _ _ _ => @associativity_sym _ _ _ _ _ _ _ _ _)
       (fun _ _ _ _ _ _ _ => @associativity _ _ _ _ _ _ _ _ _)
       (fun _ _ => @right_identity _ _ _ _)
       (fun _ _ => @left_identity _ _ _ _)
       (@identity_identity _ C).

Notation "C ^op" := (opposite C) (at level 3) : category_scope.

Definition prod `(C : @PreCategory objC, D : @PreCategory objD) : @PreCategory (objC * objD).
  refine (@Build_PreCategory'
            (C * D)%type
            (fun s d => (morphism C (fst s) (fst d)
                         * morphism D (snd s) (snd d))%type)
            (fun x => (identity (fst x), identity (snd x)))
            (fun s d d' m2 m1 => (fst m2 o fst m1, snd m2 o snd m1))
            _
            _
            _
            _
            _); admit.
Defined.
Infix "*" := prod : category_scope.

Definition compose_functor `(C : @PreCategory objC, D : @PreCategory objD, E : @PreCategory objE) (G : Functor D E) (F : Functor C D) : Functor C E
  := Build_Functor
       C E
       (fun c => G (F c))
       (fun _ _ m => morphism_of G (morphism_of F m))
       cheat
       cheat.

Infix "o" := compose_functor : functor_scope.

Record NaturalTransformation `(C : @PreCategory objC, D : @PreCategory objD) (F G : Functor C D) :=
  Build_NaturalTransformation' {
      components_of :> forall c, morphism D (F c) (G c);
      commutes : forall s d (m : morphism C s d),
                   components_of d o F _1 m = G _1 m o components_of s;

      commutes_sym : forall s d (m : C.(morphism) s d),
                       G _1 m o components_of s = components_of d o F _1 m
    }.
Definition functor_category `(C : @PreCategory objC, D : @PreCategory objD) : PreCategory
  := @Build_PreCategory' (Functor C D)
                         (@NaturalTransformation _ C _ D)
                         cheat
                         cheat
                         cheat
                         cheat
                         cheat
                         cheat
                         cheat.

Definition opposite_functor `(F : @Functor objC C objD D) : Functor C^op D^op
  := Build_Functor (C^op) (D^op)
                   (object_of F)
                   (fun s d => morphism_of F (s := d) (d := s))
                   (fun d' d s m1 m2 => composition_of F s d d' m2 m1)
                   (identity_of F).

Definition opposite_invL `(F : @Functor objC C^op objD D) : Functor C D^op
  := Build_Functor C (D^op)
                   (object_of F)
                   (fun s d => morphism_of F (s := d) (d := s))
                   (fun d' d s m1 m2 => composition_of F s d d' m2 m1)
                   (identity_of F).
Notation "F ^op" := (opposite_functor F) : functor_scope.

Notation "F ^op'L" := (opposite_invL F) (at level 3) : functor_scope.
Definition fst `{C : @PreCategory objC, D : @PreCategory objD} : Functor (C * D) C
  := Build_Functor (C * D) C
                   (@fst _ _)
                   (fun _ _ => @fst _ _)
                   (fun _ _ _ _ _ => idpath)
                   (fun _ => idpath).

Definition snd `{C : @PreCategory objC, D : @PreCategory objD} : Functor (C * D) D
  := Build_Functor (C * D) D
                   (@snd _ _)
                   (fun _ _ => @snd _ _)
                   (fun _ _ _ _ _ => idpath)
                   (fun _ => idpath).
Definition prod_functor `(F : @Functor objC C objD D, F' : @Functor objC C objD' D')
: Functor C (D * D')
  := Build_Functor
       C (D * D')
       (fun c => (F c, F' c))
       (fun s d m => (F _1 m, F' _1 m))%morphism
       cheat
       cheat.
Definition pair `(F : @Functor objC C objD D, F' : @Functor objC' C' objD' D') : Functor (C * C') (D * D')
  := (prod_functor (F o fst) (F' o snd))%functor.
Notation cat_of obj :=
  (@Build_PreCategory' obj
                       (fun x y => forall _ : x, y)
                       (fun _ x => x)
                       (fun _ _ _ f g x => f (g x))%core
                       (fun _ _ _ _ _ _ _ => idpath)
                       (fun _ _ _ _ _ _ _ => idpath)
                       (fun _ _ _ => idpath)
                       (fun _ _ _ => idpath)
                       (fun _ => idpath)).

Definition hom_functor `(C : @PreCategory objC) : Functor (C^op * C) (cat_of Type)
  := Build_Functor _ _ cheat cheat cheat cheat.

Definition induced_hom_natural_transformation `(F : @Functor objC C objD D)
: NaturalTransformation (hom_functor C) (hom_functor D o pair F^op F)
  := Build_NaturalTransformation' _ _ cheat cheat cheat.

Class IsFullyFaithful `(F : @Functor objC C objD D)
  := is_fully_faithful
     : forall x y : C,
         IsIsomorphism (induced_hom_natural_transformation F (x, y)).

Definition coyoneda `(A : @PreCategory objA) : Functor A^op (@functor_category _ A _ (cat_of Type))
  := cheat.

Definition yoneda `(A : @PreCategory objA) : Functor A (@functor_category _ A^op _ (cat_of Type))
  := (((coyoneda A^op)^op'L)^op'L)%functor.
Definition coyoneda_embedding `(A : @PreCategory objA) : @IsFullyFaithful _ _ _ _ (@coyoneda _ A).
Admitted.

Definition yoneda_embedding_fast `(A : @PreCategory objA) : @IsFullyFaithful _ _ _ _ (@yoneda _ A).
Proof.
  intros a b.
  pose proof (coyoneda_embedding A^op a b) as CYE.
  unfold yoneda.
  Time let t := (type of CYE) in
  let t' := (eval simpl in t) in pose proof ((fun (x : t) => (x : t')) CYE) as CYE'. (* Finished transaction in 0. secs (0.216013u,0.004s) *)
  Fail Timeout 1 let t := match goal with |- ?G => constr:(G) end in
  let t' := (eval simpl in t) in exact ((fun (x : t') => (x : t)) CYE').
  Time let t := match goal with |- ?G => constr:(G) end in
  let t' := (eval simpl in t) in exact ((fun (x : t') => (x : t)) CYE'). (* Finished transaction in 0. secs (0.248016u,0.s) *)
Fail Timeout 2 Defined.
Time Defined. (* Finished transaction in 1. secs (0.432027u,0.s) *)

Definition yoneda_embedding `(A : @PreCategory objA) : @IsFullyFaithful _ _ _ _ (@yoneda _ A).
Proof.
  intros a b.
  pose proof (coyoneda_embedding A^op a b) as CYE.
  unfold yoneda; simpl in *.
  Fail Timeout 1 exact CYE.
  Time exact CYE. (* Finished transaction in 0. secs (0.012001u,0.s) *)
