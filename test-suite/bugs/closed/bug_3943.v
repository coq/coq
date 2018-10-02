(* File reduced by coq-bug-finder from original input, then from 9492 lines to 119 lines *)
(* coqc version 8.5beta1 (January 2015) compiled on Jan 18 2015 7:27:36 with OCaml 3.12.1
   coqtop version 8.5beta1 (January 2015) *)

Set Typeclasses Dependency Order.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y" := (@paths _ x y) : type_scope.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.

Set Implicit Arguments.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.

Record PreCategory := Build_PreCategory' {
      object :> Type;
      morphism : object -> object -> Type;
      identity : forall x, morphism x x;
      compose : forall s d d',
                  morphism d d'
                  -> morphism s d
                  -> morphism s d' }.
Arguments identity {!C%category} / x%object : rename.
Arguments compose {!C%category} / {s d d'}%object (m1 m2)%morphism : rename.

Class IsIsomorphism {C : PreCategory} {s d} (m : morphism C s d) := {
    morphism_inverse : morphism C d s;
    left_inverse : compose morphism_inverse m = identity _;
    right_inverse : compose m morphism_inverse = identity _ }.
Arguments morphism_inverse {C s d} m {_}.
Local Notation "m ^-1" := (morphism_inverse m) (at level 3, format "m '^-1'") : morphism_scope.

Class Isomorphic {C : PreCategory} s d := {
    morphism_isomorphic :> morphism C s d;
    isisomorphism_isomorphic :> IsIsomorphism morphism_isomorphic }.
Coercion morphism_isomorphic : Isomorphic >-> morphism.

Variable C : PreCategory.
Variables s d : C.

Definition path_isomorphic (i j : Isomorphic s d)
: @morphism_isomorphic _ _ _ i = @morphism_isomorphic _ _ _ j -> i = j.
Admitted.

Definition ap_morphism_inverse_path_isomorphic (i j : Isomorphic s d) p q
: ap (fun e : Isomorphic s d => e^-1)%morphism (path_isomorphic i j p) = q.
