(* File reduced by coq-bug-finder from original input, then from 8808 lines to 424 lines, then from 432 lines to 196 lines, then from\
 145 lines to 82 lines *)
(* coqc version trunk (September 2014) compiled on Sep 18 2014 21:0:5 with OCaml 4.01.0
   coqtop version cagnode16:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (07e4438bd758c2ced8caf09a6961ccd77d84e42b) *)

Reserved Infix "o" (at level 40, left associativity).
Global Set Primitive Projections.

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
    where "f 'o' g" := (compose f g)
  }.
Arguments identity {!C%category} / x%object : rename.

Infix "o" := (@compose _ _ _ _) : morphism_scope.

Local Open Scope morphism_scope.
Definition prodC (C D : PreCategory) : PreCategory.
  refine (@Build_PreCategory
            (C * D)%type
            (fun s d => (morphism C (fst s) (fst d)
                         * morphism D (snd s) (snd d))%type)
            (fun x => (identity (fst x), identity (snd x)))
            (fun s d d' m2 m1 => (fst m2 o fst m1, snd m2 o snd m1))).
Defined.

Local Infix "*" := prodC : category_scope.

Delimit Scope functor_scope with functor.

Record Functor (C D : PreCategory) :=
  {
    object_of :> C -> D;
    morphism_of : forall s d, morphism C s d
                              -> morphism D (object_of s) (object_of d);
    identity_of : forall x, morphism_of _ _ (identity x)
                            = identity (object_of x)
  }.
Arguments morphism_of [C%category] [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.
Notation "F '_1' m" := (morphism_of F m) (at level 10, no associativity) : morphism_scope.
Axiom cheat : forall {A}, A.
Record NaturalTransformation C D (F G : Functor C D) := { components_of :> forall c, morphism D (F c) (G c) }.
Definition functor_category (C D : PreCategory) : PreCategory.
  exact (@Build_PreCategory (Functor C D)
                            (@NaturalTransformation C D) cheat cheat).
Defined.

Local Notation "C -> D" := (functor_category C D) : category_scope.
Variable C1 : PreCategory.
Variable C2 : PreCategory.
Variable D : PreCategory.

Definition functor_object_of
: (C1 -> (C2 -> D))%category -> (C1 * C2 -> D)%category.
Proof.
  intro F; hnf in F |- *.
  refine (Build_Functor
            (prodC C1 C2) D
            (fun c1c2 => F (fst c1c2) (snd c1c2))
            (fun s d m => F (fst d) _1 (snd m) o (@morphism_of _ _ F _ _ (fst m)) (snd s))
            _).
  intros.
  rewrite identity_of.
  cbn.
  rewrite (identity_of _ _ F (fst x)).
  Undo.
(* Toplevel input, characters 20-55:
Error:
Found no subterm matching "F _1 (identity (fst x))" in the current goal. *)
  rewrite identity_of. (* Toplevel input, characters 15-34:
Error:
Found no subterm matching "morphism_of ?202 (identity ?203)" in the current goal. *)
