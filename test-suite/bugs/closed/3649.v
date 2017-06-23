(* -*- coq-prog-args: ("-nois") -*- *)
(* File reduced by coq-bug-finder from original input, then from 9518 lines to 404 lines, then from 410 lines to 208 lines, then from 162 lines to 77 lines *)
(* coqc version trunk (September 2014) compiled on Sep 18 2014 21:0:5 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (07e4438bd758c2ced8caf09a6961ccd77d84e42b) *)
Declare ML Module "ltac_plugin".
Set Default Proof Mode "Classic".
Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x = y" (at level 70, no associativity).
Delimit Scope type_scope with type.
Bind Scope type_scope with Sortclass.
Open Scope type_scope.
Axiom admit : forall {T}, T.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Reserved Infix "o" (at level 40, left associativity).
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Global Set Primitive Projections.
Delimit Scope morphism_scope with morphism.
Record PreCategory :=
  { object :> Type;
    morphism : object -> object -> Type;

    identity : forall x, morphism x x;
    compose : forall s d d',
                morphism d d'
                -> morphism s d
                -> morphism s d'
    where "f 'o' g" := (compose f g) }.
Infix "o" := (@compose _ _ _ _) : morphism_scope.
Set Implicit Arguments.
Local Open Scope morphism_scope.
Record Functor (C D : PreCategory) :=
  { object_of :> C -> D;
    morphism_of : forall s d, morphism C s d
                              -> morphism D (object_of s) (object_of d) }.
Class IsIsomorphism {C : PreCategory} {s d} (m : morphism C s d) :=
  { morphism_inverse : morphism C d s }.
Record NaturalTransformation C D (F G : Functor C D) := { components_of :> forall c, morphism D (F c) (G c) }.
Definition composeT C D (F F' F'' : Functor C D) (T' : NaturalTransformation F' F'') (T : NaturalTransformation F F')
: NaturalTransformation F F''.
  exact admit.
Defined.
Definition functor_category (C D : PreCategory) : PreCategory.
  exact (@Build_PreCategory (Functor C D)
                            (@NaturalTransformation C D)
                            admit
                            (@composeT C D)).
Defined.
Goal forall (C D : PreCategory) (G G' : Functor C D)
            (T : @NaturalTransformation C D G G')
            (H : @IsIsomorphism (@functor_category C D) G G' T)
            (x : C),
       @paths (morphism D (G x) (G x))
              (@compose D (G x) (G' x) (G x)
                        ((@morphism_inverse (@functor_category C D) G G' T H) x)
                        (T x)) (@identity D (G x)).
  intros.
  (** This [change] succeeded, but did not progress, in 07e4438bd758c2ced8caf09a6961ccd77d84e42b, because [T0 x o T1 x] was not found in the goal *)
  let T0 := match goal with |- context[components_of ?T0 ?x o components_of ?T1 ?x] => constr:(T0) end in
  let T1 := match goal with |- context[components_of ?T0 ?x o components_of ?T1 ?x] => constr:(T1) end in
  progress change (T0 x o T1 x) with ((fun y => y) (T0 x o T1 x)).
