
(* -*- mode: coq; coq-prog-args: ("-nois" "-R" "." "Top" "-top" "bug_hom_anom_10") -*- *)
(* File reduced by coq-bug-finder from original input, then from 156 lines to 41 lines, then from 237 lines to 45 lines, then from 163 lines to 66 lines, then from 342 lines to 121 lines, then from 353 lines to 184 lines, then from 343 lines to 255 lines, then from 435 lines to 322 lines, then from 475 lines to 351 lines, then from 442 lines to 377 lines, then from 505 lines to 410 lines, then from 591 lines to 481 lines, then from 596 lines to 535 lines, then from 647 lines to 570 lines, then from 669 lines to 596 lines, then from 687 lines to 620 lines, then from 728 lines to 652 lines, then from 1384 lines to 683 lines, then from 984 lines to 707 lines, then from 1124 lines to 734 lines, then from 775 lines to 738 lines, then from 950 lines to 763 lines, then from 857 lines to 798 lines, then from 983 lines to 752 lines, then from 1598 lines to 859 lines, then from 873 lines to 859 lines, then from 875 lines to 862 lines, then from 901 lines to 863 lines, then from 1047 lines to 865 lines, then from 929 lines to 871 lines, then from 989 lines to 884 lines, then from 900 lines to 884 lines, then from 884 lines to 751 lines, then from 763 lines to 593 lines, then from 482 lines to 232 lines, then from 416 lines to 227 lines, then from 290 lines to 231 lines, then from 348 lines to 235 lines, then from 249 lines to 235 lines, then from 249 lines to 172 lines, then from 186 lines to 172 lines, then from 140 lines to 113 lines, then from 127 lines to 113 lines *) (* coqc version trunk (June 2016) compiled on Jun 2 2016 10:16:20 with OCaml 4.02.3
   coqtop version trunk (June 2016) *)

Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x * y" (at level 40, left associativity).
Delimit Scope type_scope with type.
Open Scope type_scope.
Global Set Universe Polymorphism.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Set Implicit Arguments.
Global Set Nonrecursive Elimination Schemes.
Record prod (A B : Type) := pair { fst : A ; snd : B }.
Notation "x * y" := (prod x y) : type_scope.
Axiom admit : forall {T}, T.
Delimit Scope function_scope with function.
Notation compose := (fun g f x => g (f x)).
Notation "g 'o' f" := (compose g%function f%function) (at level 40, left associativity) : function_scope.
Record PreCategory :=
  Build_PreCategory {
      object :> Type;
      morphism : object -> object -> Type;
      identity : forall x, morphism x x }.
Bind Scope category_scope with PreCategory.
Record Functor (C D : PreCategory) := { object_of :> C -> D }.
Bind Scope functor_scope with Functor.
Class Isomorphic {C : PreCategory} (s d : C) := {}.
Definition oppositeC (C : PreCategory) : PreCategory
  := @Build_PreCategory C (fun s d => morphism C d s) admit.
Notation "C ^op" := (oppositeC C) (at level 3, format "C '^op'") : category_scope.
Definition oppositeF C D (F : Functor C D) : Functor C^op D^op
  := Build_Functor (C^op) (D^op) (object_of F).
Definition set_cat : PreCategory := @Build_PreCategory Type (fun x y => x -> y) admit.
Definition prodC (C D : PreCategory) : PreCategory
  := @Build_PreCategory
       (C * D)%type
       (fun s d => (morphism C (fst s) (fst d)
                    * morphism D (snd s) (snd d))%type)
       admit.
Infix "*" := prodC : category_scope.
Section composition.
  Variables B C D E : PreCategory.
  Definition composeF (G : Functor D E) (F : Functor C D) : Functor C E := Build_Functor C E (fun c => G (F c)).
End composition.
Infix "o" := composeF : functor_scope.
Definition fstF {C D} : Functor (C * D) C := admit.
Definition sndF {C D} : Functor (C * D) D := admit.
Definition prodF C D D' (F : Functor C D) (F' : Functor C D') : Functor C (D * D') := admit.
Local Infix "*" := prodF : functor_scope.
Definition pairF C D C' D' (F : Functor C D) (F' : Functor C' D') : Functor (C * C') (D * D')
  := (F o fstF) * (F' o sndF).
Section hom_functor.
  Variable C : PreCategory.
  Local Notation obj_of c'c :=
    ((morphism
        C
        (fst (c'c : object (C^op * C)))
        (snd (c'c : object (C^op * C))))).
  Definition hom_functor : Functor (C^op * C) set_cat
    := Build_Functor (C^op * C) set_cat (fun c'c => obj_of c'c).
End hom_functor.
Definition identityF C : Functor C C := admit.
Definition functor_category (C D : PreCategory) : PreCategory
  := @Build_PreCategory (Functor C D) admit admit.
Local Notation "C -> D" := (functor_category C D) : category_scope.
Definition NaturalIsomorphism (C D : PreCategory) F G := @Isomorphic (C -> D) F G.

Section Adjunction.
  Variables C D : PreCategory.
  Variable F : Functor C D.
  Variable G : Functor D C.
  
  Record AdjunctionHom :=
    {
      mate_of : @NaturalIsomorphism
                  (prodC (oppositeC C) D)
                  (@set_cat)
                  (@composeF
                     (prodC (oppositeC C) D)
                     (prodC (oppositeC D) D)
                     (@set_cat) (@hom_functor D)
                     (@pairF (oppositeC C)
                             (oppositeC D) D D
                             (@oppositeF C D F) (identityF D)))
                  (@composeF
                     (prodC (oppositeC C) D)
                     (prodC (oppositeC C) C)
                     (@set_cat) (@hom_functor C)
                     (@pairF (oppositeC C)
                             (oppositeC C) D C
                             (identityF (oppositeC C)) G))
    }.
End Adjunction.
