(* File reduced by coq-bug-finder from original input, then from 11218 lines to 438 lines, then from 434 lines to 202 lines, then from 140 lines to 94 lines *)
(* coqc version trunk (September 2014) compiled on Sep 25 2014 2:53:46 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (bec7e0914f4a7144cd4efa8ffaccc9f72dbdb790) *)
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a.
Set Implicit Arguments.
Delimit Scope morphism_scope with morphism.
Record PreCategory := { object :> Type ; morphism : object -> object -> Type }.
Bind Scope category_scope with PreCategory.
Local Open Scope morphism_scope.
Record Functor (C D : PreCategory) :=
  { object_of :> C -> D;
    morphism_of : forall s d, morphism C s d -> morphism D (object_of s) (object_of d) }.
Set Primitive Projections.
Class IsIsomorphism {C : PreCategory} {s d} (m : morphism C s d) := { morphism_inverse : morphism C d s }.
Record NaturalTransformation C D (F G : Functor C D) := { components_of :> forall c, morphism D (F c) (G c) }.
Unset Primitive Projections.
Class Isomorphic {C : PreCategory} s d :=
  { morphism_isomorphic :> morphism C s d;
    isisomorphism_isomorphic :> IsIsomorphism morphism_isomorphic }.
Arguments morphism_inverse {C s d} m {_} / .
Local Notation "m ^-1" := (morphism_inverse m) (at level 3, format "m '^-1'") : morphism_scope.
Definition functor_category (C D : PreCategory) : PreCategory.
  exact (@Build_PreCategory (Functor C D)
                            (@NaturalTransformation C D)).
Defined.
Local Notation "C -> D" := (functor_category C D) : category_scope.
Generalizable All Variables.
Definition isisomorphism_components_of `{@IsIsomorphism (C -> D) F G T} x : IsIsomorphism (T x).
Proof.
  constructor.
  exact (T^-1 x).
Defined.
Hint Immediate isisomorphism_components_of : typeclass_instances.
Goal forall (x3 x9 : PreCategory) (x12 f0 : Functor x9 x3)
            (x35 : @Isomorphic (@functor_category x9 x3) f0 x12)
            (x37 : object x9)
            (H3 : morphism x3 (@object_of x9 x3 f0 x37)
                           (@object_of x9 x3 f0 x37))
            (x34 : @Isomorphic (@functor_category x9 x3) x12 f0)
            (m : morphism x3 (x12 x37) (f0 x37) ->
                 morphism x3 (f0 x37) (x12 x37) ->
                 morphism x3 (f0 x37) (f0 x37)),
       @paths
         (morphism x3 (@object_of x9 x3 f0 x37) (@object_of x9 x3 f0 x37))
         H3
         (m
            (@components_of x9 x3 x12 f0
                            (@morphism_inverse (@functor_category x9 x3) f0 x12
                                               (@morphism_isomorphic (@functor_category x9 x3) f0 x12 x35)
                                               (@isisomorphism_isomorphic (@functor_category x9 x3) f0 x12
                                                                          x35)) x37)
            (@components_of x9 x3 f0 x12
                            (@morphism_inverse (@functor_category x9 x3) x12 f0
                                               (@morphism_isomorphic (@functor_category x9 x3) x12 f0 x34)
                                               (@isisomorphism_isomorphic (@functor_category x9 x3) x12 f0
                                                                          x34)) x37)).
  Unset Printing All.
  intros.
  match goal with
    | [ |- context[components_of ?T^-1 ?x] ]
      => progress let T1 := constr:(T^-1 x) in
                  let T2 := constr:((T x)^-1) in
                  change T1 with T2 || fail 1 "too early"
  end.

  Undo.

  match goal with
    | [ |- context[components_of ?T^-1 ?x] ]
      => progress let T1 := constr:(T^-1 x) in
                  change T1 with ((T x)^-1) || fail 1 "too early 2"
  end.

  Undo.

  match goal with
    | [ |- context[components_of ?T^-1 ?x] ]
      => progress let T2 := constr:((T x)^-1) in
                  change (T^-1 x) with T2
  end. (* not convertible *)

(*

  (@components_of x9 x3 x12 f0
     (@morphism_inverse _ _ _
        (@morphism_isomorphic (functor_category x9 x3) f0 x12 x35) _) x37)

*)
